// SPDX-License-Identifier: GPL-2.0
use core::mem::{size_of, size_of_val, MaybeUninit};
use core::ops::Range;

use kernel::{
    bindings,
    file::{File, FileDescriptorReservation},
    io_buffer::{IoBufferReader, ReadableFromBytes, WritableToBytes},
    pages::Pages,
    prelude::*,
    sync::Arc,
    types::ARef,
    user_ptr::UserSlicePtrReader,
};

use crate::{
    defs::*,
    node::{Node, NodeRef},
    process::Process,
};

#[derive(Default)]
pub(crate) struct AllocationInfo {
    /// Range within the allocation where we can find the offsets to the object descriptors.
    pub(crate) offsets: Option<Range<usize>>,
    /// The target node of the transaction this allocation is associated to.
    /// Not set for replies.
    pub(crate) target_node: Option<NodeRef>,
    /// When this allocation is dropped, call `pending_oneway_finished` on the node.
    ///
    /// This is used to serialize oneway transaction on the same node. Binder guarantees that
    /// oneway transactions to the same node are delivered sequentially in the order they are sent.
    pub(crate) oneway_node: Option<Arc<Node>>,
    /// Zero the data in the buffer on free.
    pub(crate) clear_on_free: bool,
    /// List of files embedded in this transaction.
    file_list: FileList,
}

/// Represents an allocation that the kernel is currently using.
///
/// When allocations are idle, the range allocator holds the data related to them.
pub(crate) struct Allocation {
    pub(crate) offset: usize,
    size: usize,
    pub(crate) ptr: usize,
    pages: Arc<Vec<Pages<0>>>,
    pub(crate) process: Arc<Process>,
    allocation_info: Option<AllocationInfo>,
    free_on_drop: bool,
}

impl Allocation {
    pub(crate) fn new(
        process: Arc<Process>,
        offset: usize,
        size: usize,
        ptr: usize,
        pages: Arc<Vec<Pages<0>>>,
    ) -> Self {
        Self {
            process,
            offset,
            size,
            ptr,
            pages,
            allocation_info: None,
            free_on_drop: true,
        }
    }

    fn iterate<T>(&self, mut offset: usize, mut size: usize, mut cb: T) -> Result
    where
        T: FnMut(&Pages<0>, usize, usize) -> Result,
    {
        // Check that the request is within the buffer.
        if offset.checked_add(size).ok_or(EINVAL)? > self.size {
            return Err(EINVAL);
        }
        offset += self.offset;
        let mut page_index = offset >> bindings::PAGE_SHIFT;
        offset &= (1 << bindings::PAGE_SHIFT) - 1;
        while size > 0 {
            let available = core::cmp::min(size, (1 << bindings::PAGE_SHIFT) - offset);
            cb(&self.pages[page_index], offset, available)?;
            size -= available;
            page_index += 1;
            offset = 0;
        }
        Ok(())
    }

    pub(crate) fn copy_into(
        &self,
        reader: &mut UserSlicePtrReader,
        offset: usize,
        size: usize,
    ) -> Result {
        self.iterate(offset, size, |page, offset, to_copy| {
            page.copy_into_page(reader, offset, to_copy)
        })
    }

    pub(crate) fn read<T: ReadableFromBytes>(&self, offset: usize) -> Result<T> {
        let mut out = MaybeUninit::<T>::uninit();
        let mut out_offset = 0;
        self.iterate(offset, size_of::<T>(), |page, offset, to_copy| {
            // SAFETY: The sum of `offset` and `to_copy` is bounded by the size of T.
            let obj_ptr = unsafe { (out.as_mut_ptr() as *mut u8).add(out_offset) };
            // SAFETY: The pointer points is in-bounds of the `out` variable, so it is valid.
            unsafe { page.read(obj_ptr, offset, to_copy) }?;
            out_offset += to_copy;
            Ok(())
        })?;
        // SAFETY: We just initialised the data.
        Ok(unsafe { out.assume_init() })
    }

    pub(crate) fn write<T: ?Sized>(&self, offset: usize, obj: &T) -> Result {
        let mut obj_offset = 0;
        self.iterate(offset, size_of_val(obj), |page, offset, to_copy| {
            // SAFETY: The sum of `offset` and `to_copy` is bounded by the size of T.
            let obj_ptr = unsafe { (obj as *const T as *const u8).add(obj_offset) };
            // SAFETY: We have a reference to the object, so the pointer is valid.
            unsafe { page.write(obj_ptr, offset, to_copy) }?;
            obj_offset += to_copy;
            Ok(())
        })
    }

    pub(crate) fn fill_zero(&self) -> Result {
        self.iterate(0, self.size, |page, offset, len| {
            page.fill_zero(offset, len)
        })
    }

    pub(crate) fn keep_alive(mut self) {
        self.process
            .buffer_make_freeable(self.offset, self.allocation_info.take());
        self.free_on_drop = false;
    }

    pub(crate) fn set_info(&mut self, info: AllocationInfo) {
        self.allocation_info = Some(info);
    }

    pub(crate) fn get_or_init_info(&mut self) -> &mut AllocationInfo {
        self.allocation_info.get_or_insert_with(Default::default)
    }

    pub(crate) fn set_info_offsets(&mut self, offsets: Range<usize>) {
        self.get_or_init_info().offsets = Some(offsets);
    }

    pub(crate) fn set_info_oneway_node(&mut self, oneway_node: Arc<Node>) {
        self.get_or_init_info().oneway_node = Some(oneway_node);
    }

    pub(crate) fn set_info_clear_on_drop(&mut self) {
        self.get_or_init_info().clear_on_free = true;
    }

    pub(crate) fn set_info_target_node(&mut self, target_node: NodeRef) {
        self.get_or_init_info().target_node = Some(target_node);
    }

    pub(crate) fn info_add_fd(&mut self, file: ARef<File>, buffer_offset: usize) -> Result {
        self.get_or_init_info()
            .file_list
            .files_to_translate
            .try_push(FileEntry {
                file,
                buffer_offset,
            })?;

        Ok(())
    }

    pub(crate) fn translate_fds(&mut self) -> Result<TranslatedFds> {
        let file_list = match self.allocation_info.as_mut() {
            Some(info) => &mut info.file_list,
            None => return Ok(TranslatedFds::new()),
        };

        let files = core::mem::take(&mut file_list.files_to_translate);
        let mut reservations = Vec::try_with_capacity(files.len())?;
        for file_info in files {
            let res = FileDescriptorReservation::new(bindings::O_CLOEXEC)?;
            self.write::<u32>(file_info.buffer_offset, &res.reserved_fd())?;
            reservations.try_push(Reservation {
                res,
                file: file_info.file,
            })?;
        }

        Ok(TranslatedFds { reservations })
    }
}

impl Drop for Allocation {
    fn drop(&mut self) {
        if !self.free_on_drop {
            return;
        }

        if let Some(mut info) = self.allocation_info.take() {
            if let Some(oneway_node) = info.oneway_node.as_ref() {
                oneway_node.pending_oneway_finished();
            }

            info.target_node = None;

            if let Some(offsets) = info.offsets.clone() {
                let view = AllocationView::new(self, offsets.start);
                for i in offsets.step_by(size_of::<usize>()) {
                    if view.cleanup_object(i).is_err() {
                        pr_warn!("Error cleaning up object at offset {}\n", i)
                    }
                }
            }

            if info.clear_on_free {
                match self.fill_zero() {
                    Err(e) => pr_warn!("Failed to clear data on free: {:?}", e),
                    Ok(()) => (),
                }
            }
        }

        self.process.buffer_raw_free(self.ptr);
    }
}

/// A view into the beginning of an allocation.
///
/// All attempts to read or write outside of the view will fail. To intentionally access outside of
/// this view, use the `alloc` field of this struct directly.
pub(crate) struct AllocationView<'a> {
    pub(crate) alloc: &'a mut Allocation,
    limit: usize,
}

impl<'a> AllocationView<'a> {
    pub(crate) fn new(alloc: &'a mut Allocation, limit: usize) -> Self {
        AllocationView { alloc, limit }
    }

    pub(crate) fn read<T: ReadableFromBytes>(&self, offset: usize) -> Result<T> {
        if offset.checked_add(size_of::<T>()).ok_or(EINVAL)? > self.limit {
            return Err(EINVAL);
        }
        self.alloc.read(offset)
    }

    pub(crate) fn write<T: WritableToBytes>(&self, offset: usize, obj: &T) -> Result {
        if offset.checked_add(size_of::<T>()).ok_or(EINVAL)? > self.limit {
            return Err(EINVAL);
        }
        self.alloc.write(offset, obj)
    }

    pub(crate) fn transfer_binder_object(
        &self,
        offset: usize,
        obj: &bindings::flat_binder_object,
        strong: bool,
        node_ref: NodeRef,
    ) -> Result {
        if Arc::ptr_eq(&node_ref.node.owner, &self.alloc.process) {
            // The receiving process is the owner of the node, so send it a binder object (instead
            // of a handle).
            let (ptr, cookie) = node_ref.node.get_id();
            let mut newobj = FlatBinderObject::default();
            newobj.hdr.type_ = if strong {
                BINDER_TYPE_BINDER
            } else {
                BINDER_TYPE_WEAK_BINDER
            };
            newobj.flags = obj.flags;
            newobj.__bindgen_anon_1.binder = ptr as _;
            newobj.cookie = cookie as _;
            self.write(offset, &newobj)?;
            // Increment the user ref count on the node. It will be decremented as part of the
            // destruction of the buffer, when we see a binder or weak-binder object.
            node_ref.node.update_refcount(true, 1, strong);
        } else {
            // The receiving process is different from the owner, so we need to insert a handle to
            // the binder object.
            let handle = self
                .alloc
                .process
                .insert_or_update_handle(node_ref, false)?;
            let mut newobj = FlatBinderObject::default();
            newobj.hdr.type_ = if strong {
                BINDER_TYPE_HANDLE
            } else {
                BINDER_TYPE_WEAK_HANDLE
            };
            newobj.flags = obj.flags;
            newobj.__bindgen_anon_1.handle = handle;
            if self.write(offset, &newobj).is_err() {
                // Decrement ref count on the handle we just created.
                let _ = self.alloc.process.update_ref(handle, false, strong);
                return Err(EINVAL);
            }
        }
        Ok(())
    }

    fn cleanup_object(&self, index_offset: usize) -> Result {
        let offset = self.alloc.read(index_offset)?;
        let header = self.read::<BinderObjectHeader>(offset)?;
        match header.type_ {
            BINDER_TYPE_WEAK_BINDER | BINDER_TYPE_BINDER => {
                let obj = self.read::<FlatBinderObject>(offset)?;
                let strong = header.type_ == BINDER_TYPE_BINDER;
                // SAFETY: The type is `BINDER_TYPE_{WEAK_}BINDER`, so the `binder` field is
                // populated.
                let ptr = unsafe { obj.__bindgen_anon_1.binder } as usize;
                let cookie = obj.cookie as usize;
                self.alloc.process.update_node(ptr, cookie, strong);
                Ok(())
            }
            BINDER_TYPE_WEAK_HANDLE | BINDER_TYPE_HANDLE => {
                let obj = self.read::<FlatBinderObject>(offset)?;
                let strong = header.type_ == BINDER_TYPE_HANDLE;
                // SAFETY: The type is `BINDER_TYPE_{WEAK_}HANDLE`, so the `handle` field is
                // populated.
                let handle = unsafe { obj.__bindgen_anon_1.handle } as _;
                self.alloc.process.update_ref(handle, false, strong)
            }
            _ => Ok(()),
        }
    }
}

/// A binder object as it is serialized.
///
/// # Invariants
///
/// All bytes must be initialized, and the value of `self.hdr.type_` must be one of the allowed
/// types.
#[repr(C)]
pub(crate) union BinderObject {
    hdr: bindings::binder_object_header,
    fbo: bindings::flat_binder_object,
    fdo: bindings::binder_fd_object,
    bbo: bindings::binder_buffer_object,
    fdao: bindings::binder_fd_array_object,
}

/// A view into a `BinderObject` that can be used in a match statement.
pub(crate) enum BinderObjectRef<'a> {
    Binder(&'a mut bindings::flat_binder_object),
    Handle(&'a mut bindings::flat_binder_object),
    Fd(&'a mut bindings::binder_fd_object),
    Ptr(&'a mut bindings::binder_buffer_object),
    Fda(&'a mut bindings::binder_fd_array_object),
}

impl BinderObject {
    pub(crate) fn read_from(reader: &mut UserSlicePtrReader) -> Result<BinderObject> {
        let object = Self::read_from_inner(|slice| {
            let read_len = usize::min(slice.len(), reader.len());
            // SAFETY: The length we pass to `read_raw` is at most the length of the slice.
            unsafe {
                reader
                    .clone_reader()
                    .read_raw(slice.as_mut_ptr(), read_len)?;
            }
            Ok(())
        })?;

        // If we used a object type smaller than the largest object size, then we've read more
        // bytes than we needed to. However, we used `.clone_reader()` to avoid advancing the
        // original reader. Now, we call `skip` so that the caller's reader is advanced by the
        // right amount.
        //
        // The `skip` call fails if the reader doesn't have `size` bytes available. This could
        // happen if the type header corresponds to an object type that is larger than the rest of
        // the reader.
        //
        // Any extra bytes beyond the size of the object are inaccessible after this call, so
        // reading them again from the `reader` later does not result in TOCTOU bugs.
        reader.skip(object.size())?;

        Ok(object)
    }

    /// Use the provided reader closure to construct a `BinderObject`.
    ///
    /// The closure should write the bytes for the object into the provided slice.
    pub(crate) fn read_from_inner<R>(reader: R) -> Result<BinderObject>
    where
        R: FnOnce(&mut [u8; size_of::<BinderObject>()]) -> Result<()>,
    {
        let mut obj = MaybeUninit::<BinderObject>::zeroed();

        // SAFETY: The lengths of `BinderObject` and `[u8; size_of::<BinderObject>()]` are equal,
        // and the byte array has an alignment requirement of one, so the pointer cast is okay.
        // Additionally, `obj` was initialized to zeros, so the byte array will not be
        // uninitialized.
        (reader)(unsafe { &mut *obj.as_mut_ptr().cast() })?;

        // SAFETY: The entire object is initialized, so accessing this field is safe.
        let type_ = unsafe { obj.assume_init_ref().hdr.type_ };
        if Self::type_to_size(type_).is_none() {
            // The value of `obj.hdr_type_` was invalid.
            return Err(EINVAL);
        }

        // SAFETY: All bytes are initialized (since we zeroed them at the start) and we checked
        // that `self.hdr.type_` is one of the allowed types, so the type invariants are satisfied.
        unsafe { Ok(obj.assume_init()) }
    }

    pub(crate) fn as_ref(&mut self) -> BinderObjectRef<'_> {
        use BinderObjectRef::*;
        // SAFETY: The constructor ensures that all bytes of `self` are initialized, and all
        // variants of this union accept all initialized bit patterns.
        unsafe {
            match self.hdr.type_ {
                BINDER_TYPE_WEAK_BINDER | BINDER_TYPE_BINDER => Binder(&mut self.fbo),
                BINDER_TYPE_WEAK_HANDLE | BINDER_TYPE_HANDLE => Handle(&mut self.fbo),
                BINDER_TYPE_FD => Fd(&mut self.fdo),
                BINDER_TYPE_PTR => Ptr(&mut self.bbo),
                BINDER_TYPE_FDA => Fda(&mut self.fdao),
                // SAFETY: By the type invariant, the value of `self.hdr.type_` cannot have any
                // other value than the ones checked above.
                _ => core::hint::unreachable_unchecked(),
            }
        }
    }

    pub(crate) fn size(&self) -> usize {
        // SAFETY: The entire object is initialized, so accessing this field is safe.
        let type_ = unsafe { self.hdr.type_ };

        // SAFETY: The type invariants guarantee that the type field is correct.
        unsafe { Self::type_to_size(type_).unwrap_unchecked() }
    }

    fn type_to_size(type_: u32) -> Option<usize> {
        match type_ {
            BINDER_TYPE_WEAK_BINDER => Some(size_of::<bindings::flat_binder_object>()),
            BINDER_TYPE_BINDER => Some(size_of::<bindings::flat_binder_object>()),
            BINDER_TYPE_WEAK_HANDLE => Some(size_of::<bindings::flat_binder_object>()),
            BINDER_TYPE_HANDLE => Some(size_of::<bindings::flat_binder_object>()),
            BINDER_TYPE_FD => Some(size_of::<bindings::binder_fd_object>()),
            BINDER_TYPE_PTR => Some(size_of::<bindings::binder_buffer_object>()),
            BINDER_TYPE_FDA => Some(size_of::<bindings::binder_fd_array_object>()),
            _ => None,
        }
    }
}

#[derive(Default)]
struct FileList {
    files_to_translate: Vec<FileEntry>,
}

struct FileEntry {
    /// The file for which a descriptor will be created in the recipient process.
    file: ARef<File>,
    /// The offset in the buffer where the file descriptor is stored.
    buffer_offset: usize,
}

pub(crate) struct TranslatedFds {
    reservations: Vec<Reservation>,
}

struct Reservation {
    res: FileDescriptorReservation,
    file: ARef<File>,
}

impl TranslatedFds {
    pub(crate) fn new() -> Self {
        Self {
            reservations: Vec::new(),
        }
    }

    pub(crate) fn commit(self) {
        for entry in self.reservations {
            entry.res.commit(entry.file);
        }
    }
}
