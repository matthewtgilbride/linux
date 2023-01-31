// SPDX-License-Identifier: GPL-2.0

use core::{
    alloc::AllocError,
    mem::{size_of, MaybeUninit},
    sync::atomic::{AtomicU32, Ordering},
};
use kernel::{
    bindings,
    file::{File, PollTable},
    io_buffer::{IoBufferReader, IoBufferWriter},
    linked_list::{GetLinks, Links, List},
    prelude::*,
    security,
    sync::{CondVar, Ref, SpinLock, UniqueRef},
    user_ptr::{UserSlicePtr, UserSlicePtrReader, UserSlicePtrWriter},
    Either,
};

use crate::{
    allocation::{Allocation, AllocationView},
    defs::*,
    process::{AllocationInfo, Process},
    ptr_align,
    transaction::{FileInfo, Transaction},
    DeliverCode, DeliverToRead, DeliverToReadListAdapter,
};

pub(crate) type BinderResult<T = ()> = core::result::Result<T, BinderError>;

#[derive(Debug)]
pub(crate) struct BinderError {
    pub(crate) reply: u32,
}

impl BinderError {
    pub(crate) fn new_failed() -> Self {
        Self {
            reply: BR_FAILED_REPLY,
        }
    }

    pub(crate) fn new_dead() -> Self {
        Self {
            reply: BR_DEAD_REPLY,
        }
    }
}

impl From<Error> for BinderError {
    fn from(_: Error) -> Self {
        Self::new_failed()
    }
}

impl From<AllocError> for BinderError {
    fn from(_: AllocError) -> Self {
        Self::new_failed()
    }
}

/// Stores the layout of the scatter-gather entries. This is used during the `translate_objects`
/// call and is discarded when it returns.
struct ScatterGatherState {
    /// A struct that tracks the amount of unused buffer space.
    unused_buffer_space: UnusedBufferSpace,
    /// Scatter-gather entries to copy.
    sg_entries: Vec<ScatterGatherEntry>,
    /// Indexes into `sg_entries` corresponding to the last binder_buffer_object that
    /// was processed and all of its ancestors. The array is in sorted order.
    ancestors: Vec<usize>,
}

/// This entry specifies an additional buffer that should be copied using the scatter-gather
/// mechanism.
struct ScatterGatherEntry {
    /// The index in the offset array of the BINDER_TYPE_PTR that this entry originates from.
    obj_index: usize,
    /// Offset in target buffer.
    offset: usize,
    /// User address in source buffer.
    sender_uaddr: usize,
    /// Number of bytes to copy.
    length: usize,
    /// The minimum offset of the next fixup in this buffer.
    fixup_min_offset: usize,
    /// The offsets within this buffer that contain pointers which should be translated.
    pointer_fixups: Vec<PointerFixupEntry>,
}

/// This entry specifies that a fixup should happen at `target_offset` of the
/// buffer. If `skip` is nonzero, then the fixup is a `binder_fd_array_object`
/// and is applied later. Otherwise if `skip` is zero, then the size of the
/// fixup is `sizeof::<u64>()` and `pointer_value` is written to the buffer.
struct PointerFixupEntry {
    /// The number of bytes to skip, or zero for a `binder_buffer_object` fixup.
    skip: usize,
    /// The translated pointer to write when `skip` is zero.
    pointer_value: u64,
    /// The offset at which the value should be written. The offset is relative
    /// to the original buffer.
    target_offset: usize,
}

/// Return type of `apply_and_validate_fixup_in_parent`.
struct ParentFixupInfo {
    /// The index of the parent buffer in `sg_entries`.
    parent_sg_index: usize,
    /// The number of ancestors of the buffer.
    ///
    /// The buffer is considered an ancestor of itself, so this is always at
    /// least one.
    num_ancestors: usize,
    /// New value of `fixup_min_offset` if this fixup is applied.
    new_min_offset: usize,
    /// The offset of the fixup in the target buffer.
    target_offset: usize,
}

impl ScatterGatherState {
    /// Called when a `binder_buffer_object` or `binder_fd_array_object` tries
    /// to access a region in its parent buffer. These accesses have various
    /// restrictions, which this method verifies.
    ///
    /// The `parent_offset` and `length` arguments describe the offset and
    /// length of the access in the parent buffer.
    ///
    /// # Detailed restrictions
    ///
    /// Obviously the fixup must be in-bounds for the parent buffer.
    ///
    /// For safety reasons, we only allow fixups inside a buffer to happen
    /// at increasing offsets; additionally, we only allow fixup on the last
    /// buffer object that was verified, or one of its parents.
    ///
    /// Example of what is allowed:
    ///
    /// A
    ///   B (parent = A, offset = 0)
    ///   C (parent = A, offset = 16)
    ///     D (parent = C, offset = 0)
    ///   E (parent = A, offset = 32) // min_offset is 16 (C.parent_offset)
    ///
    /// Examples of what is not allowed:
    ///
    /// Decreasing offsets within the same parent:
    /// A
    ///   C (parent = A, offset = 16)
    ///   B (parent = A, offset = 0) // decreasing offset within A
    ///
    /// Referring to a parent that wasn't the last object or any of its parents:
    /// A
    ///   B (parent = A, offset = 0)
    ///   C (parent = A, offset = 0)
    ///   C (parent = A, offset = 16)
    ///     D (parent = B, offset = 0) // B is not A or any of A's parents
    fn validate_parent_fixup(
        &self,
        parent: usize,
        parent_offset: usize,
        length: usize,
    ) -> Result<ParentFixupInfo> {
        // Using `position` would also be correct, but `rposition` avoids
        // quadratic running times.
        let ancestors_i = self
            .ancestors
            .iter()
            .copied()
            .rposition(|sg_idx| self.sg_entries[sg_idx].obj_index == parent)
            .ok_or(EINVAL)?;

        let sg_idx = self.ancestors[ancestors_i];
        let sg_entry = match self.sg_entries.get(sg_idx) {
            Some(sg_entry) => sg_entry,
            None => {
                pr_err!(
                    "self.ancestors[{}] is {}, but self.sg_entries.len() is {}",
                    ancestors_i,
                    sg_idx,
                    self.sg_entries.len()
                );
                return Err(EINVAL);
            }
        };

        if sg_entry.fixup_min_offset > parent_offset {
            pr_warn!(
                "validate_parent_fixup: fixup_min_offset={}, parent_offset={}",
                sg_entry.fixup_min_offset,
                parent_offset);
            return Err(EINVAL);
        }

        let new_min_offset = parent_offset.checked_add(length).ok_or(EINVAL)?;
        if new_min_offset > sg_entry.length {
            pr_warn!(
                "validate_parent_fixup: new_min_offset={}, sg_entry.length={}",
                new_min_offset,
                sg_entry.length);
            return Err(EINVAL);
        }

        let target_offset = sg_entry.offset.checked_add(parent_offset).ok_or(EINVAL)?;

        // The `ancestors_i + 1` operation can't overflow since the result is
        // at most `self.ancestors.len()`, which also fits in an usize.
        Ok(ParentFixupInfo {
            parent_sg_index: sg_idx,
            num_ancestors: ancestors_i + 1,
            new_min_offset,
            target_offset,
        })
    }
}

/// Keeps track of how much unused buffer space is left. The initial amount is the number of bytes
/// requested by the user using the `buffers_size` field of `binder_transaction_data_sg`. Each time
/// we translate an object of type `BINDER_TYPE_PTR`, some of the unused buffer space is consumed.
struct UnusedBufferSpace {
    /// The start of the remaining space.
    offset: usize,
    /// The end of the remaining space.
    limit: usize,
}

impl UnusedBufferSpace {
    /// Claim the next `size` bytes from the unused buffer space. The offset for the claimed chunk
    /// into the buffer is returned.
    fn claim_next(&mut self, size: usize) -> Result<usize> {
        // We require every chunk to be aligned.
        let size = ptr_align(size);
        let new_offset = self.offset.checked_add(size).ok_or(EINVAL)?;

        if new_offset <= self.limit {
            let offset = self.offset;
            self.offset = new_offset;
            Ok(offset)
        } else {
            Err(EINVAL)
        }
    }
}

const LOOPER_REGISTERED: u32 = 0x01;
const LOOPER_ENTERED: u32 = 0x02;
const LOOPER_EXITED: u32 = 0x04;
const LOOPER_INVALID: u32 = 0x08;
const LOOPER_WAITING: u32 = 0x10;
const LOOPER_POLL: u32 = 0x20;

struct InnerThread {
    /// Determines the looper state of the thread. It is a bit-wise combination of the constants
    /// prefixed with `LOOPER_`.
    looper_flags: u32,

    /// Determines whether the looper should return.
    looper_need_return: bool,

    /// Determines if thread is dead.
    is_dead: bool,

    /// Work item used to deliver error codes to the thread that started a transaction. When set to
    /// `Some(x)`, it will hold the only reference to the object so that it can update the error
    /// code to be delivered before queuing it.
    reply_work: Option<Ref<ThreadError>>,

    /// Work item used to deliver error codes to the current thread. When set to `Some(x)`, it will
    /// hold the only reference to the object so that it can update the error code to be delivered
    /// before queuing.
    return_work: Option<Ref<ThreadError>>,

    /// Determines whether the work list below should be processed. When set to false, `work_list`
    /// is treated as if it were empty.
    process_work_list: bool,
    work_list: List<DeliverToReadListAdapter>,
    current_transaction: Option<Ref<Transaction>>,
}

impl InnerThread {
    fn new() -> Self {
        Self {
            looper_flags: 0,
            looper_need_return: false,
            is_dead: false,
            process_work_list: false,
            work_list: List::new(),
            current_transaction: None,
            return_work: None,
            reply_work: None,
        }
    }

    fn set_reply_work(&mut self, reply_work: Ref<ThreadError>) {
        self.reply_work = Some(reply_work);
    }

    fn push_reply_work(&mut self, code: u32) {
        let work = self.reply_work.take();
        self.push_existing_work(work, code);
    }

    fn set_return_work(&mut self, return_work: Ref<ThreadError>) {
        self.return_work = Some(return_work);
    }

    fn push_return_work(&mut self, code: u32) {
        let work = self.return_work.take();
        self.push_existing_work(work, code);
    }

    fn push_existing_work(&mut self, owork: Option<Ref<ThreadError>>, code: u32) {
        // TODO: Write some warning when the following fails. It should not happen, and
        // if it does, there is likely something wrong.
        if let Some(work) = owork {
            // `error_code` is written to with relaxed semantics because the queue onto which it is
            // being inserted is protected by a lock. The release barrier when the lock is released
            // by the caller matches with the acquire barrier of the future reader to guarantee
            // that `error_code` is visible.
            work.error_code.store(code, Ordering::Relaxed);
            self.push_work(work);
        }
    }

    fn pop_work(&mut self) -> Option<Ref<dyn DeliverToRead>> {
        if !self.process_work_list {
            return None;
        }

        let ret = self.work_list.pop_front();
        // Once the queue is drained, we stop processing it until a non-deferred item is pushed
        // again onto it.
        self.process_work_list = !self.work_list.is_empty();
        ret
    }

    fn push_work_deferred(&mut self, work: Ref<dyn DeliverToRead>) {
        self.work_list.push_back(work);
    }

    fn push_work(&mut self, work: Ref<dyn DeliverToRead>) {
        self.push_work_deferred(work);
        self.process_work_list = true;
    }

    fn has_work(&self) -> bool {
        self.process_work_list && !self.work_list.is_empty()
    }

    /// Fetches the transaction the thread can reply to. If the thread has a pending transaction
    /// (that it could respond to) but it has also issued a transaction, it must first wait for the
    /// previously-issued transaction to complete.
    fn pop_transaction_to_reply(&mut self, thread: &Thread) -> Result<Ref<Transaction>> {
        let transaction = self.current_transaction.take().ok_or(EINVAL)?;

        if core::ptr::eq(thread, transaction.from.as_ref()) {
            self.current_transaction = Some(transaction);
            return Err(EINVAL);
        }

        // Find a new current transaction for this thread.
        self.current_transaction = transaction.find_from(thread);
        Ok(transaction)
    }

    fn pop_transaction_replied(&mut self, transaction: &Ref<Transaction>) -> bool {
        match self.current_transaction.take() {
            None => false,
            Some(old) => {
                if !Ref::ptr_eq(transaction, &old) {
                    self.current_transaction = Some(old);
                    return false;
                }
                self.current_transaction = old.clone_next();
                true
            }
        }
    }

    fn looper_enter(&mut self) {
        self.looper_flags |= LOOPER_ENTERED;
        if self.looper_flags & LOOPER_REGISTERED != 0 {
            self.looper_flags |= LOOPER_INVALID;
        }
    }

    fn looper_register(&mut self, valid: bool) {
        self.looper_flags |= LOOPER_REGISTERED;
        if !valid || self.looper_flags & LOOPER_ENTERED != 0 {
            self.looper_flags |= LOOPER_INVALID;
        }
    }

    fn looper_exit(&mut self) {
        self.looper_flags |= LOOPER_EXITED;
    }

    /// Determines whether the thread is part of a pool, i.e., if it is a looper.
    fn is_looper(&self) -> bool {
        self.looper_flags & (LOOPER_ENTERED | LOOPER_REGISTERED) != 0
    }

    /// Determines whether the thread should attempt to fetch work items from the process queue
    /// (when its own queue is empty). This is case when the thread is not part of a transaction
    /// stack and it is registered as a looper.
    fn should_use_process_work_queue(&self) -> bool {
        self.current_transaction.is_none() && self.is_looper()
    }

    fn poll(&mut self) -> u32 {
        self.looper_flags |= LOOPER_POLL;
        if self.has_work() {
            bindings::POLLIN
        } else {
            0
        }
    }
}

pub(crate) struct Thread {
    pub(crate) id: i32,
    pub(crate) process: Ref<Process>,
    inner: SpinLock<InnerThread>,
    work_condvar: CondVar,
    links: Links<Thread>,
}

impl Thread {
    pub(crate) fn new(id: i32, process: Ref<Process>) -> Result<Ref<Self>> {
        let return_work = Ref::try_new(ThreadError::new(InnerThread::set_return_work))?;
        let reply_work = Ref::try_new(ThreadError::new(InnerThread::set_reply_work))?;
        let mut thread = Pin::from(UniqueRef::try_new(Self {
            id,
            process,
            // SAFETY: `inner` is initialised in the call to `spinlock_init` below.
            inner: unsafe { SpinLock::new(InnerThread::new()) },
            // SAFETY: `work_condvar` is initialised in the call to `condvar_init` below.
            work_condvar: unsafe { CondVar::new() },
            links: Links::new(),
        })?);

        // SAFETY: `inner` is pinned when `thread` is.
        let inner = unsafe { thread.as_mut().map_unchecked_mut(|t| &mut t.inner) };
        kernel::spinlock_init!(inner, "Thread::inner");

        // SAFETY: `work_condvar` is pinned when `thread` is.
        let condvar = unsafe { thread.as_mut().map_unchecked_mut(|t| &mut t.work_condvar) };
        kernel::condvar_init!(condvar, "Thread::work_condvar");

        {
            let mut inner = thread.inner.lock();
            inner.set_reply_work(reply_work);
            inner.set_return_work(return_work);
        }

        Ok(thread.into())
    }

    pub(crate) fn set_current_transaction(&self, transaction: Ref<Transaction>) {
        self.inner.lock().current_transaction = Some(transaction);
    }

    /// Attempts to fetch a work item from the thread-local queue. The behaviour if the queue is
    /// empty depends on `wait`: if it is true, the function waits for some work to be queued (or a
    /// signal); otherwise it returns indicating that none is available.
    fn get_work_local(self: &Ref<Self>, wait: bool) -> Result<Option<Ref<dyn DeliverToRead>>> {
        // Try once if the caller does not want to wait.
        if !wait {
            return self.inner.lock().pop_work().ok_or(EAGAIN).map(Some);
        }

        // Loop waiting only on the local queue (i.e., not registering with the process queue).
        let mut inner = self.inner.lock();
        loop {
            if let Some(work) = inner.pop_work() {
                return Ok(Some(work));
            }

            inner.looper_flags |= LOOPER_WAITING;
            inner.looper_need_return = false;
            let signal_pending = self.work_condvar.wait(&mut inner);
            inner.looper_flags &= !LOOPER_WAITING;

            if signal_pending {
                return Err(ERESTARTSYS);
            }
            if inner.looper_need_return {
                return Ok(None);
            }
        }
    }

    /// Attempts to fetch a work item from the thread-local queue, falling back to the process-wide
    /// queue if none is available locally.
    ///
    /// This must only be called when the thread is not participating in a transaction chain. If it
    /// is, the local version (`get_work_local`) should be used instead.
    fn get_work(self: &Ref<Self>, wait: bool) -> Result<Option<Ref<dyn DeliverToRead>>> {
        // Try to get work from the thread's work queue, using only a local lock.
        {
            let mut inner = self.inner.lock();
            if let Some(work) = inner.pop_work() {
                return Ok(Some(work));
            }
        }

        // If the caller doesn't want to wait, try to grab work from the process queue.
        //
        // We know nothing will have been queued directly to the thread queue because it is not in
        // a transaction and it is not in the process' ready list.
        if !wait {
            return self.process.get_work().ok_or(EAGAIN).map(Some);
        }

        // Get work from the process queue. If none is available, atomically register as ready.
        let reg = match self.process.get_work_or_register(self) {
            Either::Left(work) => return Ok(Some(work)),
            Either::Right(reg) => reg,
        };

        let mut inner = self.inner.lock();
        loop {
            if let Some(work) = inner.pop_work() {
                return Ok(Some(work));
            }

            inner.looper_flags |= LOOPER_WAITING;
            inner.looper_need_return = false;
            let signal_pending = self.work_condvar.wait(&mut inner);
            inner.looper_flags &= !LOOPER_WAITING;

            if signal_pending {
                // A signal is pending. We need to pull the thread off the list, then check the
                // state again after it's off the list to ensure that something was not queued in
                // the meantime. If something has been queued, we just return it (instead of the
                // error).
                drop(inner);
                drop(reg);
                return self.inner.lock().pop_work().ok_or(ERESTARTSYS).map(Some);
            }
            if inner.looper_need_return {
                drop(inner);
                drop(reg);
                return Ok(None);
            }
        }
    }

    pub(crate) fn push_work(&self, work: Ref<dyn DeliverToRead>) -> BinderResult {
        {
            let mut inner = self.inner.lock();
            if inner.is_dead {
                return Err(BinderError::new_dead());
            }
            inner.push_work(work);
        }
        self.work_condvar.notify_one();
        Ok(())
    }

    /// Attempts to push to given work item to the thread if it's a looper thread (i.e., if it's
    /// part of a thread pool) and is alive. Otherwise, push the work item to the process instead.
    pub(crate) fn push_work_if_looper(&self, work: Ref<dyn DeliverToRead>) -> BinderResult {
        let mut inner = self.inner.lock();
        if inner.is_looper() && !inner.is_dead {
            inner.push_work(work);
            Ok(())
        } else {
            drop(inner);
            self.process.push_work(work)
        }
    }

    pub(crate) fn push_work_deferred(&self, work: Ref<dyn DeliverToRead>) {
        self.inner.lock().push_work_deferred(work);
    }

    fn translate_object(
        &self,
        obj_index: usize,
        offset: usize,
        object: BinderObjectRef<'_>,
        view: &mut AllocationView<'_, '_>,
        allow_fds: bool,
        sg_state: &mut ScatterGatherState,
    ) -> BinderResult {
        // TODO: Handle other types.
        match object {
            BinderObjectRef::Binder(obj) => {
                let strong = obj.hdr.type_ == BINDER_TYPE_BINDER;

                // SAFETY: `binder` is a `binder_uintptr_t`; any bit pattern is a valid
                // representation.
                let ptr = unsafe { obj.__bindgen_anon_1.binder } as _;
                let cookie = obj.cookie as _;
                let flags = obj.flags as _;
                let node = self.process.as_ref_borrow().get_node(
                    ptr,
                    cookie,
                    flags,
                    strong,
                    Some(self),
                )?;
                security::binder_transfer_binder(&self.process.cred, &view.alloc.process.cred)?;

                view.transfer_binder_object(offset, obj, strong, node)?;
            }
            BinderObjectRef::Handle(obj) => {
                let strong = obj.hdr.type_ == BINDER_TYPE_HANDLE;

                // SAFETY: `handle` is a `u32`; any bit pattern is a valid representation.
                let handle = unsafe { obj.__bindgen_anon_1.handle } as _;
                let node = self.process.get_node_from_handle(handle, strong)?;
                security::binder_transfer_binder(&self.process.cred, &view.alloc.process.cred)?;

                view.transfer_binder_object(offset, obj, strong, node)?;
            }
            BinderObjectRef::Fd(obj) => {
                if !allow_fds {
                    return Err(BinderError::new_failed());
                }

                // SAFETY: `fd` is a `u32`; any bit pattern is a valid representation.
                let fd = unsafe { obj.__bindgen_anon_1.fd };
                let file = File::from_fd(fd)?;
                security::binder_transfer_file(
                    &self.process.cred,
                    &view.alloc.process.cred,
                    &file,
                )?;

                // To avoid leaking the sender's fd, we zero that field.
                obj.__bindgen_anon_1.fd = u32::MAX;
                view.write::<bindings::binder_fd_object>(offset, &*obj)?;

                let field_offset =
                    kernel::offset_of!(bindings::binder_fd_object, __bindgen_anon_1.fd) as usize;
                let file_info = Box::try_new(FileInfo::new(file, offset + field_offset))?;
                view.alloc.add_file_info(file_info);
            }
            BinderObjectRef::Ptr(obj) => {
                let obj_length = obj.length.try_into().map_err(|_| EINVAL)?;
                let alloc_offset = match sg_state.unused_buffer_space.claim_next(obj_length) {
                    Ok(alloc_offset) => alloc_offset,
                    Err(err) => {
                        pr_warn!(
                            "Failed to claim space for a BINDER_TYPE_PTR. (offset: {}, limit: {}, size: {})",
                            sg_state.unused_buffer_space.offset,
                            sg_state.unused_buffer_space.limit,
                            obj_length,
                        );
                        return Err(err.into());
                    },
                };

                let sg_state_idx = sg_state.sg_entries.len();
                sg_state
                    .sg_entries
                    .try_push(ScatterGatherEntry {
                        obj_index,
                        offset: alloc_offset,
                        sender_uaddr: obj.buffer as _,
                        length: obj_length,
                        pointer_fixups: Vec::new(),
                        fixup_min_offset: 0,
                    })
                    .map_err(|_| ENOMEM)?;

                let buffer_ptr_in_user_space = (view.alloc.ptr + alloc_offset) as u64;

                if obj.flags & bindings::BINDER_BUFFER_FLAG_HAS_PARENT == 0 {
                    sg_state.ancestors.clear();
                    sg_state
                        .ancestors
                        .try_push(sg_state_idx)
                        .map_err(|_| ENOMEM)?;
                } else {
                    // Another buffer also has a pointer to this buffer, and we need to fixup that
                    // pointer too.

                    let parent_index = usize::try_from(obj.parent).map_err(|_| EINVAL)?;
                    let parent_offset = usize::try_from(obj.parent_offset).map_err(|_| EINVAL)?;

                    let info = sg_state.validate_parent_fixup(
                        parent_index,
                        parent_offset,
                        size_of::<u64>(),
                    )?;

                    sg_state.ancestors.truncate(info.num_ancestors);
                    sg_state
                        .ancestors
                        .try_push(sg_state_idx)
                        .map_err(|_| ENOMEM)?;

                    let parent_entry = match sg_state.sg_entries.get_mut(info.parent_sg_index) {
                        Some(parent_entry) => parent_entry,
                        None => {
                            pr_err!(
                                "validate_parent_fixup returned index out of bounds for sg.entries"
                            );
                            return Err(EINVAL.into());
                        }
                    };

                    parent_entry.fixup_min_offset = info.new_min_offset;
                    parent_entry
                        .pointer_fixups
                        .try_push(PointerFixupEntry {
                            skip: 0,
                            pointer_value: buffer_ptr_in_user_space,
                            target_offset: info.target_offset,
                        })
                        .map_err(|_| ENOMEM)?;
                }

                // Update pointer in `binder_buffer_object`.
                obj.buffer = buffer_ptr_in_user_space;
                if let Err(err) = view.write::<bindings::binder_buffer_object>(offset, &*obj) {
                    pr_warn!("Failed to write BINDER_TYPE_PTR to view: {:?}", err);
                    return Err(err.into());
                }
            }
            BinderObjectRef::Fda(obj) => {
                let parent_index = usize::try_from(obj.parent).map_err(|_| EINVAL)?;
                let parent_offset = usize::try_from(obj.parent_offset).map_err(|_| EINVAL)?;
                let num_fds = usize::try_from(obj.num_fds).map_err(|_| EINVAL)?;
                let fds_len = num_fds.checked_mul(size_of::<u32>()).ok_or(EINVAL)?;

                let info = sg_state.validate_parent_fixup(parent_index, parent_offset, fds_len)?;

                sg_state.ancestors.truncate(info.num_ancestors);
                let parent_entry = match sg_state.sg_entries.get_mut(info.parent_sg_index) {
                    Some(parent_entry) => parent_entry,
                    None => {
                        pr_err!(
                            "validate_parent_fixup returned index out of bounds for sg.entries"
                        );
                        return Err(EINVAL.into());
                    }
                };

                parent_entry.fixup_min_offset = info.new_min_offset;
                parent_entry
                    .pointer_fixups
                    .try_push(PointerFixupEntry {
                        skip: fds_len,
                        pointer_value: 0,
                        target_offset: info.target_offset,
                    })
                    .map_err(|_| ENOMEM)?;

                let fda_uaddr = parent_entry
                    .sender_uaddr
                    .checked_add(parent_offset)
                    .ok_or(EINVAL)?;
                let fda_bytes = unsafe { UserSlicePtr::new(fda_uaddr as _, fds_len) }.read_all()?;

                if fds_len != fda_bytes.len() {
                    pr_err!("UserSlicePtr::read_all returned wrong length in BINDER_TYPE_FDA");
                    return Err(EINVAL.into());
                }

                for i in (0..fds_len).step_by(size_of::<u32>()) {
                    let fd = {
                        let mut fd_bytes = [0u8; size_of::<u32>()];
                        fd_bytes.copy_from_slice(&fda_bytes[i..i + size_of::<u32>()]);
                        u32::from_ne_bytes(fd_bytes)
                    };

                    let file = File::from_fd(fd)?;
                    security::binder_transfer_file(
                        &self.process.cred,
                        &view.alloc.process.cred,
                        &file,
                    )?;

                    // The `validate_parent_fixup` call ensuers that this addition will not
                    // overflow.
                    let file_info = Box::try_new(FileInfo::new(file, info.target_offset + i))?;
                    view.alloc.add_file_info(file_info);
                }
                drop(fda_bytes);

                view.write::<bindings::binder_fd_array_object>(offset, &*obj)?;
            }
        }

        Ok(())
    }

    fn apply_sg(
        &self,
        alloc: &mut Allocation<'_>,
        sg_state: &mut ScatterGatherState,
    ) -> BinderResult {
        for sg_entry in &mut sg_state.sg_entries {
            let mut end_of_previous_fixup = sg_entry.offset;
            let offset_end = sg_entry.offset.checked_add(sg_entry.length).ok_or(EINVAL)?;

            let mut reader =
                unsafe { UserSlicePtr::new(sg_entry.sender_uaddr as _, sg_entry.length) }.reader();
            for fixup in &mut sg_entry.pointer_fixups {
                let fixup_len = if fixup.skip == 0 {
                    size_of::<u64>()
                } else {
                    fixup.skip
                };

                let target_offset_end = fixup.target_offset.checked_add(fixup_len).ok_or(EINVAL)?;

                if fixup.target_offset < end_of_previous_fixup || offset_end < target_offset_end {
                    pr_warn!("Fixups oob {} {} {} {}",
                             fixup.target_offset,
                             end_of_previous_fixup,
                             offset_end,
                             target_offset_end);
                    return Err(EINVAL.into());
                }

                let copy_off = end_of_previous_fixup;
                let copy_len = fixup.target_offset - end_of_previous_fixup;
                if let Err(err) = alloc.copy_into(&mut reader, copy_off, copy_len) {
                    pr_warn!("Failed copying into alloc: {:?}", err);
                    return Err(err.into());
                }
                if fixup.skip == 0 {
                    if let Err(err) = alloc.write::<u64>(fixup.target_offset, &fixup.pointer_value) {
                        pr_warn!("Failed copying ptr into alloc: {:?}", err);
                        return Err(err.into());
                    }
                }
                if let Err(err) = reader.skip(fixup_len) {
                    pr_warn!("Failed skipping {} from reader: {:?}", fixup_len, err);
                    return Err(err.into());
                }
                end_of_previous_fixup = target_offset_end;
            }

            let copy_off = end_of_previous_fixup;
            let copy_len = offset_end - end_of_previous_fixup;
            if let Err(err) = alloc.copy_into(&mut reader, copy_off, copy_len) {
                pr_warn!("Failed copying remainder into alloc: {:?}", err);
                return Err(err.into());
            }
        }
        Ok(())
    }

    pub(crate) fn copy_transaction_data<'a>(
        &self,
        to_process: &'a Process,
        tr: &BinderTransactionDataSg,
        allow_fds: bool,
        txn_security_ctx_offset: Option<&mut usize>,
    ) -> BinderResult<Allocation<'a>> {
        let trd = &tr.transaction_data;

        let mut secctx = if let Some(offset) = txn_security_ctx_offset {
            let secid = self.process.cred.get_secid();
            let ctx = match security::SecurityCtx::from_secid(secid) {
                Ok(ctx) => ctx,
                Err(err) => {
                    pr_warn!("Failed to get security ctx for id {}: {:?}", secid, err);
                    return Err(err.into());
                },
            };
            Some((offset, ctx))
        } else {
            None
        };

        let data_size = trd.data_size.try_into().map_err(|_| EINVAL)?;
        let adata_size = ptr_align(data_size);
        let offsets_size = trd.offsets_size.try_into().map_err(|_| EINVAL)?;
        let aoffsets_size = ptr_align(offsets_size);
        let buffers_size = tr.buffers_size.try_into().map_err(|_| EINVAL)?;
        let abuffers_size = ptr_align(buffers_size);
        let asecctx_size = secctx.as_ref().map(|(_, ctx)| ptr_align(ctx.len())).unwrap_or(0);

        // This guarantees that at least `sizeof(usize)` bytes will be allocated.
        let len = core::cmp::max(
            adata_size
                .checked_add(aoffsets_size)
                .and_then(|sum| sum.checked_add(abuffers_size))
                .and_then(|sum| sum.checked_add(asecctx_size))
                .ok_or(ENOMEM)?,
            size_of::<usize>(),
        );
        let secctx_off = adata_size + aoffsets_size + abuffers_size;
        let mut alloc = to_process.buffer_alloc(len)?;

        let mut buffer_reader =
            unsafe { UserSlicePtr::new(trd.data.ptr.buffer as _, data_size) }.reader();
        let mut end_of_previous_object = 0;
        let mut sg_state = None;

        // Copy offsets if there are any.
        if offsets_size > 0 {
            {
                let mut reader =
                    unsafe { UserSlicePtr::new(trd.data.ptr.offsets as _, offsets_size) }.reader();
                alloc.copy_into(&mut reader, adata_size, offsets_size)?;
            }

            let offsets_start = adata_size;
            let offsets_end = adata_size + aoffsets_size;

            // This state is used for BINDER_TYPE_PTR objects.
            sg_state = Some(ScatterGatherState {
                unused_buffer_space: UnusedBufferSpace {
                    offset: offsets_end,
                    limit: len,
                },
                sg_entries: Vec::new(),
                ancestors: Vec::new(),
            });
            let sg_state = sg_state.as_mut().unwrap();

            // Traverse the objects specified.
            let mut view = AllocationView::new(&mut alloc, data_size);
            for (index, index_offset) in (offsets_start..offsets_end)
                .step_by(size_of::<usize>())
                .enumerate()
            {
                let offset = view.alloc.read(index_offset)?;

                // Copy data between two objects.
                if end_of_previous_object < offset {
                    view.alloc.copy_into(
                        &mut buffer_reader,
                        end_of_previous_object,
                        offset - end_of_previous_object,
                    )?;
                }

                let mut object = BinderObject::read_from(&mut buffer_reader)?;

                match self.translate_object(
                    index,
                    offset,
                    object.as_ref()?,
                    &mut view,
                    allow_fds,
                    sg_state,
                ) {
                    Ok(()) => end_of_previous_object = offset + object.size()?,
                    Err(err) => {
                        pr_warn!("Error while translating object.");
                        alloc.set_info(AllocationInfo {
                            offsets: offsets_start..index_offset,
                        });
                        return Err(err);
                    }
                }
            }
            alloc.set_info(AllocationInfo {
                offsets: offsets_start..offsets_end,
            });
        }

        // Copy remaining raw data.
        alloc.copy_into(
            &mut buffer_reader,
            end_of_previous_object,
            data_size - end_of_previous_object,
        )?;

        if let Some(sg_state) = sg_state.as_mut() {
            if let Err(err) = self.apply_sg(&mut alloc, sg_state) {
                pr_warn!("Failure in apply_sg: {:?}", err);
                return Err(err.into());
            }
        }

        if let Some((off_out, secctx)) = secctx.as_mut() {
            if let Err(err) = alloc.write(secctx_off, secctx.as_bytes()) {
                pr_warn!("Failed to write security context: {:?}", err);
                return Err(err.into());
            }
            **off_out = secctx_off;
        }

        Ok(alloc)
    }

    fn unwind_transaction_stack(self: &Ref<Self>) {
        let mut thread = self.clone();
        while let Ok(transaction) = {
            let mut inner = thread.inner.lock();
            inner.pop_transaction_to_reply(thread.as_ref())
        } {
            let reply = Either::Right(BR_DEAD_REPLY);
            if !transaction.from.deliver_single_reply(reply, &transaction) {
                break;
            }

            thread = transaction.from.clone();
        }
    }

    pub(crate) fn deliver_reply(
        &self,
        reply: Either<Ref<Transaction>, u32>,
        transaction: &Ref<Transaction>,
    ) {
        if self.deliver_single_reply(reply, transaction) {
            transaction.from.unwind_transaction_stack();
        }
    }

    /// Delivers a reply to the thread that started a transaction. The reply can either be a
    /// reply-transaction or an error code to be delivered instead.
    ///
    /// Returns whether the thread is dead. If it is, the caller is expected to unwind the
    /// transaction stack by completing transactions for threads that are dead.
    fn deliver_single_reply(
        &self,
        reply: Either<Ref<Transaction>, u32>,
        transaction: &Ref<Transaction>,
    ) -> bool {
        {
            let mut inner = self.inner.lock();
            if !inner.pop_transaction_replied(transaction) {
                return false;
            }

            if inner.is_dead {
                return true;
            }

            match reply {
                Either::Left(work) => inner.push_work(work),
                Either::Right(code) => inner.push_reply_work(code),
            }
        }

        // Notify the thread now that we've released the inner lock.
        self.work_condvar.notify_one();
        false
    }

    /// Determines if the given transaction is the current transaction for this thread.
    fn is_current_transaction(&self, transaction: &Ref<Transaction>) -> bool {
        let inner = self.inner.lock();
        match &inner.current_transaction {
            None => false,
            Some(current) => Ref::ptr_eq(current, transaction),
        }
    }

    fn transaction<T>(self: &Ref<Self>, tr: &BinderTransactionDataSg, inner: T)
    where
        T: FnOnce(&Ref<Self>, &BinderTransactionDataSg) -> BinderResult,
    {
        if let Err(err) = inner(self, tr) {
            pr_warn!("Transaction failed: {}", err.reply);
            self.inner.lock().push_return_work(err.reply);
        }
    }

    fn reply_inner(self: &Ref<Self>, tr: &BinderTransactionDataSg) -> BinderResult {
        let orig = self.inner.lock().pop_transaction_to_reply(self)?;
        if !orig.from.is_current_transaction(&orig) {
            return Err(BinderError::new_failed());
        }

        // We need to complete the transaction even if we cannot complete building the reply.
        (|| -> BinderResult<_> {
            let completion = Ref::try_new(DeliverCode::new(BR_TRANSACTION_COMPLETE))?;
            let process = orig.from.process.clone();
            let allow_fds = orig.flags & TF_ACCEPT_FDS != 0;
            let reply = Transaction::new_reply(self, process, tr, allow_fds)?;
            self.inner.lock().push_work(completion);
            orig.from.deliver_reply(Either::Left(reply), &orig);
            Ok(())
        })()
        .map_err(|mut err| {
            // At this point we only return `BR_TRANSACTION_COMPLETE` to the caller, and we must let
            // the sender know that the transaction has completed (with an error in this case).
            pr_warn!("Failure during reply - delivering BR_FAILED_REPLY to sender.");
            let reply = Either::Right(BR_FAILED_REPLY);
            orig.from.deliver_reply(reply, &orig);
            err.reply = BR_TRANSACTION_COMPLETE;
            err
        })
    }

    /// Determines the current top of the transaction stack. It fails if the top is in another
    /// thread (i.e., this thread belongs to a stack but it has called another thread). The top is
    /// [`None`] if the thread is not currently participating in a transaction stack.
    fn top_of_transaction_stack(&self) -> Result<Option<Ref<Transaction>>> {
        let inner = self.inner.lock();
        Ok(if let Some(cur) = &inner.current_transaction {
            if core::ptr::eq(self, cur.from.as_ref()) {
                return Err(EINVAL);
            }
            Some(cur.clone())
        } else {
            None
        })
    }

    fn oneway_transaction_inner(self: &Ref<Self>, tr: &BinderTransactionDataSg) -> BinderResult {
        let handle = unsafe { tr.transaction_data.target.handle };
        let node_ref = self.process.get_transaction_node(handle)?;
        security::binder_transaction(&self.process.cred, &node_ref.node.owner.cred)?;
        let completion = Ref::try_new(DeliverCode::new(BR_TRANSACTION_COMPLETE))?;
        let transaction = Transaction::new(node_ref, None, self, tr)?;
        self.inner.lock().push_work(completion);
        // TODO: Remove the completion on error?
        transaction.submit()?;
        Ok(())
    }

    fn transaction_inner(self: &Ref<Self>, tr: &BinderTransactionDataSg) -> BinderResult {
        let handle = unsafe { tr.transaction_data.target.handle };
        let node_ref = self.process.get_transaction_node(handle)?;
        security::binder_transaction(&self.process.cred, &node_ref.node.owner.cred)?;
        // TODO: We need to ensure that there isn't a pending transaction in the work queue. How
        // could this happen?
        let top = self.top_of_transaction_stack()?;
        let completion = Ref::try_new(DeliverCode::new(BR_TRANSACTION_COMPLETE))?;
        let transaction = Transaction::new(node_ref, top, self, tr)?;

        // Check that the transaction stack hasn't changed while the lock was released, then update
        // it with the new transaction.
        {
            let mut inner = self.inner.lock();
            if !transaction.is_stacked_on(&inner.current_transaction) {
                return Err(BinderError::new_failed());
            }
            inner.current_transaction = Some(transaction.clone());
        }

        // We push the completion as a deferred work so that we wait for the reply before returning
        // to userland.
        self.push_work_deferred(completion);
        // TODO: Remove completion if submission fails?
        transaction.submit()?;
        Ok(())
    }

    fn write(self: &Ref<Self>, req: &mut BinderWriteRead) -> Result {
        let write_start = req.write_buffer.wrapping_add(req.write_consumed);
        let write_len = req.write_size - req.write_consumed;
        let mut reader = unsafe { UserSlicePtr::new(write_start as _, write_len as _).reader() };

        while reader.len() >= size_of::<u32>() && self.inner.lock().return_work.is_some() {
            let before = reader.len();
            let cmd = reader.read::<u32>()?;
            match cmd {
                BC_TRANSACTION => {
                    let tr = reader.read::<BinderTransactionData>()?.with_buffers_size(0);
                    if tr.transaction_data.flags & TF_ONE_WAY != 0 {
                        self.transaction(&tr, Self::oneway_transaction_inner)
                    } else {
                        self.transaction(&tr, Self::transaction_inner)
                    }
                }
                BC_TRANSACTION_SG => {
                    let tr = reader.read::<BinderTransactionDataSg>()?;
                    if tr.transaction_data.flags & TF_ONE_WAY != 0 {
                        self.transaction(&tr, Self::oneway_transaction_inner)
                    } else {
                        self.transaction(&tr, Self::transaction_inner)
                    }
                }
                BC_REPLY => {
                    let tr = reader.read::<BinderTransactionData>()?.with_buffers_size(0);
                    self.transaction(&tr, Self::reply_inner)
                }
                BC_REPLY_SG => {
                    let tr = reader.read::<BinderTransactionDataSg>()?;
                    self.transaction(&tr, Self::reply_inner)
                }
                BC_FREE_BUFFER => drop(self.process.buffer_get(reader.read()?)),
                BC_INCREFS => self.process.update_ref(reader.read()?, true, false)?,
                BC_ACQUIRE => self.process.update_ref(reader.read()?, true, true)?,
                BC_RELEASE => self.process.update_ref(reader.read()?, false, true)?,
                BC_DECREFS => self.process.update_ref(reader.read()?, false, false)?,
                BC_INCREFS_DONE => self.process.inc_ref_done(&mut reader, false)?,
                BC_ACQUIRE_DONE => self.process.inc_ref_done(&mut reader, true)?,
                BC_REQUEST_DEATH_NOTIFICATION => self.process.request_death(&mut reader, self)?,
                BC_CLEAR_DEATH_NOTIFICATION => self.process.clear_death(&mut reader, self)?,
                BC_DEAD_BINDER_DONE => self.process.dead_binder_done(reader.read()?, self),
                BC_REGISTER_LOOPER => {
                    let valid = self.process.register_thread();
                    self.inner.lock().looper_register(valid);
                }
                BC_ENTER_LOOPER => self.inner.lock().looper_enter(),
                BC_EXIT_LOOPER => self.inner.lock().looper_exit(),

                // BC_ATTEMPT_ACQUIRE and BC_ACQUIRE_RESULT are no longer supported.
                _ => return Err(EINVAL),
            }

            // Update the number of write bytes consumed.
            req.write_consumed += (before - reader.len()) as u64;
        }
        Ok(())
    }

    fn read(self: &Ref<Self>, req: &mut BinderWriteRead, wait: bool) -> Result {
        let read_start = req.read_buffer.wrapping_add(req.read_consumed);
        let read_len = req.read_size - req.read_consumed;
        let mut writer = unsafe { UserSlicePtr::new(read_start as _, read_len as _) }.writer();
        let (in_pool, getter) = {
            let inner = self.inner.lock();
            (
                inner.is_looper(),
                if inner.should_use_process_work_queue() {
                    Self::get_work
                } else {
                    Self::get_work_local
                },
            )
        };

        // Reserve some room at the beginning of the read buffer so that we can send a
        // BR_SPAWN_LOOPER if we need to.
        if req.read_consumed == 0 {
            writer.write(&BR_NOOP)?;
        }

        // Loop doing work while there is room in the buffer.
        let initial_len = writer.len();
        while writer.len() >= size_of::<u32>() {
            match getter(self, wait && initial_len == writer.len()) {
                Ok(Some(work)) => {
                    if !work.do_work(self, &mut writer)? {
                        break;
                    }
                }
                Ok(None) => {
                    break;
                }
                Err(err) => {
                    // Propagate the error if we haven't written anything else.
                    if initial_len == writer.len() {
                        return Err(err);
                    } else {
                        break;
                    }
                }
            }
        }

        req.read_consumed += read_len - writer.len() as u64;

        // Write BR_SPAWN_LOOPER if the process needs more threads for its pool.
        if in_pool && self.process.needs_thread() {
            let mut writer =
                unsafe { UserSlicePtr::new(req.read_buffer as _, req.read_size as _) }.writer();
            writer.write(&BR_SPAWN_LOOPER)?;
        }

        Ok(())
    }

    pub(crate) fn write_read(self: &Ref<Self>, data: UserSlicePtr, wait: bool) -> Result {
        let (mut reader, mut writer) = data.reader_writer();
        let mut req = reader.read::<BinderWriteRead>()?;

        // TODO: `write(&req)` happens in all exit paths from here on. Find a better way to encode
        // it.

        // Go through the write buffer.
        if req.write_size > 0 {
            if let Err(err) = self.write(&mut req) {
                pr_warn!("Write failure {:?}", err);
                req.read_consumed = 0;
                writer.write(&req)?;
                return Err(err);
            }
        }

        // Go through the work queue.
        let mut ret = Ok(());
        if req.read_size > 0 {
            ret = self.read(&mut req, wait);
            if ret.is_err() {
                pr_warn!("Read failure {:?}", ret);
            }
        }

        // Write the request back so that the consumed fields are visible to the caller.
        writer.write(&req)?;
        ret
    }

    pub(crate) fn poll(&self, file: &File, table: &PollTable) -> (bool, u32) {
        // SAFETY: `free_waiters` is called on release.
        unsafe { table.register_wait(file, &self.work_condvar) };
        let mut inner = self.inner.lock();
        (inner.should_use_process_work_queue(), inner.poll())
    }

    pub(crate) fn notify_flush(&self) {
        let mut inner = self.inner.lock();
        let notify = inner.looper_flags & LOOPER_WAITING != 0;
        if notify {
            inner.looper_need_return = true;
        }
        drop(inner);

        if notify {
            self.work_condvar.notify_one();
        }
    }

    pub(crate) fn notify_if_poll_ready(&self) {
        // Determine if we need to notify. This requires the lock.
        let inner = self.inner.lock();
        let notify = inner.looper_flags & LOOPER_POLL != 0
            && inner.should_use_process_work_queue()
            && !inner.has_work();
        drop(inner);

        // Now that the lock is no longer held, notify the waiters if we have to.
        if notify {
            self.work_condvar.notify_one();
        }
    }

    pub(crate) fn push_return_work(&self, code: u32) {
        self.inner.lock().push_return_work(code)
    }

    pub(crate) fn release(self: &Ref<Self>) {
        // Mark the thread as dead.
        self.inner.lock().is_dead = true;

        // Cancel all pending work items.
        while let Ok(Some(work)) = self.get_work_local(false) {
            work.cancel();
        }

        // Complete the transaction stack as far as we can.
        self.unwind_transaction_stack();

        // Remove epoll items if polling was ever used on the thread.
        let poller = self.inner.lock().looper_flags & LOOPER_POLL != 0;
        if poller {
            self.work_condvar.free_waiters();

            unsafe { bindings::synchronize_rcu() };
        }
    }
}

impl GetLinks for Thread {
    type EntryType = Thread;
    fn get_links(data: &Thread) -> &Links<Thread> {
        &data.links
    }
}

struct ThreadError {
    error_code: AtomicU32,
    return_fn: fn(&mut InnerThread, Ref<ThreadError>),
    links: Links<dyn DeliverToRead>,
}

impl ThreadError {
    fn new(return_fn: fn(&mut InnerThread, Ref<ThreadError>)) -> Self {
        Self {
            error_code: AtomicU32::new(BR_OK),
            return_fn,
            links: Links::new(),
        }
    }
}

impl DeliverToRead for ThreadError {
    fn do_work(self: Ref<Self>, thread: &Thread, writer: &mut UserSlicePtrWriter) -> Result<bool> {
        // See `ThreadInner::push_existing_work` for the reason why `error_code` is up to date even
        // though we use relaxed semantics.
        let code = self.error_code.load(Ordering::Relaxed);

        // Return the `ThreadError` to the thread.
        (self.return_fn)(&mut *thread.inner.lock(), self);

        // Deliver the error code to userspace.
        writer.write(&code)?;
        Ok(true)
    }

    fn get_links(&self) -> &Links<dyn DeliverToRead> {
        &self.links
    }
}

#[repr(C)]
union BinderObject {
    hdr: bindings::binder_object_header,
    fbo: bindings::flat_binder_object,
    fdo: bindings::binder_fd_object,
    bbo: bindings::binder_buffer_object,
    fdao: bindings::binder_fd_array_object,
}

enum BinderObjectRef<'a> {
    Binder(&'a mut bindings::flat_binder_object),
    Handle(&'a mut bindings::flat_binder_object),
    Fd(&'a mut bindings::binder_fd_object),
    Ptr(&'a mut bindings::binder_buffer_object),
    Fda(&'a mut bindings::binder_fd_array_object),
}

impl BinderObject {
    fn read_from(reader: &mut UserSlicePtrReader) -> Result<BinderObject> {
        // Create a zeroed binder object.
        //
        // Safety: All bit patterns are valid for all variants of this union. By zeroing the data
        // and not providing any way of deinitializing it, we ensure that uninitialized data is
        // never read.
        let mut obj = unsafe { MaybeUninit::<BinderObject>::zeroed().assume_init() };

        // Safety: The length is at most the size of the variable.
        //
        // Since the variable is already zeroed, all of its bytes remain initialized regardless of
        // how short `len` is.
        unsafe {
            let len = core::cmp::min(size_of::<BinderObject>(), reader.len());
            reader
                .clone_reader()
                .read_raw((&mut obj) as *mut BinderObject as *mut u8, len)?;
        }

        // If we used a object type smaller than the largest object size, then we've read more
        // bytes than we needed to. However, we used `.clone_reader()` to avoid advancing the
        // original reader. Now, we call `skip` so that the caller's reader is advanced by the
        // right amount.
        //
        // The `skip` call fails if the reader doesn't have `size` bytes available.
        reader.skip(obj.size()?)?;

        Ok(obj)
    }

    fn size(&self) -> Result<usize> {
        // Safety: The entire object is initialized, so accessing this field is safe.
        let type_ = unsafe { self.hdr.type_ };

        match type_ {
            BINDER_TYPE_WEAK_BINDER => Ok(size_of::<bindings::flat_binder_object>()),
            BINDER_TYPE_BINDER => Ok(size_of::<bindings::flat_binder_object>()),
            BINDER_TYPE_WEAK_HANDLE => Ok(size_of::<bindings::flat_binder_object>()),
            BINDER_TYPE_HANDLE => Ok(size_of::<bindings::flat_binder_object>()),
            BINDER_TYPE_FD => Ok(size_of::<bindings::binder_fd_object>()),
            BINDER_TYPE_PTR => Ok(size_of::<bindings::binder_buffer_object>()),
            BINDER_TYPE_FDA => Ok(size_of::<bindings::binder_fd_array_object>()),
            _ => Err(EINVAL),
        }
    }

    fn as_ref(&mut self) -> Result<BinderObjectRef<'_>> {
        use BinderObjectRef::*;
        // Safety: The constructor ensures that all bytes of `self` are initialized, and all
        // variants are valid for all bit patterns.
        unsafe {
            match self.hdr.type_ {
                BINDER_TYPE_WEAK_BINDER | BINDER_TYPE_BINDER => Ok(Binder(&mut self.fbo)),
                BINDER_TYPE_WEAK_HANDLE | BINDER_TYPE_HANDLE => Ok(Handle(&mut self.fbo)),
                BINDER_TYPE_FD => Ok(Fd(&mut self.fdo)),
                BINDER_TYPE_PTR => Ok(Ptr(&mut self.bbo)),
                BINDER_TYPE_FDA => Ok(Fda(&mut self.fdao)),
                _ => Err(EINVAL),
            }
        }
    }
}
