// SPDX-License-Identifier: GPL-2.0

use kernel::{
    io_buffer::IoBufferWriter,
    linked_list::{Links, List},
    prelude::*,
    sync::lock::{spinlock::SpinLockBackend, Guard},
    sync::{Arc, LockedBy},
    user_ptr::UserSlicePtrWriter,
};

use crate::{
    defs::*,
    error::{BinderError, BinderResult},
    process::{Process, ProcessInner},
    thread::Thread,
    transaction::Transaction,
    DeliverToRead, DeliverToReadListAdapter,
};

struct CountState {
    /// The reference count.
    count: usize,
    /// Whether the process that owns this node thinks that we hold a refcount on it. (Note that
    /// even if count is greater than one, we only increment it once in the owning process.)
    has_count: bool,
}

impl CountState {
    fn new() -> Self {
        Self {
            count: 0,
            has_count: false,
        }
    }
}

struct NodeInner {
    strong: CountState,
    weak: CountState,
    oneway_todo: List<DeliverToReadListAdapter>,
    has_pending_oneway_todo: bool,
    /// The number of active BR_INCREFS or BR_ACQUIRE operations. (should be maximum two)
    ///
    /// If this is non-zero, then we postpone any BR_RELEASE or BR_DECREFS notifications until the
    /// active operations have ended. This avoids the situation an increment and decrement get
    /// reordered from userspace's perspective.
    active_inc_refs: u8,
}

pub(crate) struct Node {
    pub(crate) global_id: u64,
    ptr: usize,
    cookie: usize,
    pub(crate) flags: u32,
    pub(crate) owner: Arc<Process>,
    inner: LockedBy<NodeInner, ProcessInner>,
    links: Links<dyn DeliverToRead>,
}

impl Node {
    pub(crate) fn new(ptr: usize, cookie: usize, flags: u32, owner: Arc<Process>) -> Self {
        use core::sync::atomic::{AtomicU64, Ordering};
        static NEXT_ID: AtomicU64 = AtomicU64::new(1);

        Self {
            global_id: NEXT_ID.fetch_add(1, Ordering::Relaxed),
            inner: LockedBy::new(
                &owner.inner,
                NodeInner {
                    strong: CountState::new(),
                    weak: CountState::new(),
                    oneway_todo: List::new(),
                    has_pending_oneway_todo: false,
                    active_inc_refs: 0,
                },
            ),
            ptr,
            cookie,
            flags,
            owner,
            links: Links::new(),
        }
    }

    pub(crate) fn get_id(&self) -> (usize, usize) {
        (self.ptr, self.cookie)
    }

    pub(crate) fn inc_ref_done_locked(
        &self,
        _strong: bool,
        owner_inner: &mut ProcessInner,
    ) -> bool {
        let inner = self.inner.access_mut(owner_inner);
        if inner.active_inc_refs == 0 {
            pr_err!("inc_ref_done called when no active inc_refs");
            return false;
        }

        inner.active_inc_refs -= 1;
        if inner.active_inc_refs == 0 {
            // Having active inc_refs can inhibit dropping of ref-counts. Calculate whether we
            // would send a refcount decrement, and if so, tell the caller to schedule us.
            let strong = inner.strong.count > 0;
            let has_strong = inner.strong.has_count;
            let weak = strong || inner.weak.count > 0;
            let has_weak = inner.weak.has_count;

            let should_drop_weak = !weak && has_weak;
            let should_drop_strong = !strong && has_strong;

            // If we want to drop the ref-count again, tell the caller to schedule a work node for
            // that.
            should_drop_weak || should_drop_strong
        } else {
            false
        }
    }

    pub(crate) fn update_refcount_locked(
        &self,
        inc: bool,
        strong: bool,
        count: usize,
        owner_inner: &mut ProcessInner,
    ) -> bool {
        let is_dead = owner_inner.is_dead;
        let inner = self.inner.access_mut(owner_inner);

        // Get a reference to the state we'll update.
        let state = if strong {
            &mut inner.strong
        } else {
            &mut inner.weak
        };

        // Update the count and determine whether we need to push work.
        if inc {
            state.count += count;
            !is_dead && !state.has_count
        } else {
            if state.count < count {
                pr_err!("Failure: refcount underflow!");
                return false;
            }
            state.count -= count;
            !is_dead && state.count == 0 && state.has_count
        }
    }

    pub(crate) fn update_refcount(self: &Arc<Self>, inc: bool, count: usize, strong: bool) {
        self.owner
            .inner
            .lock()
            .update_node_refcount(self, inc, strong, count, None);
    }

    pub(crate) fn populate_counts(
        &self,
        out: &mut BinderNodeInfoForRef,
        guard: &Guard<'_, ProcessInner, SpinLockBackend>,
    ) {
        let inner = self.inner.access(guard);
        out.strong_count = inner.strong.count as _;
        out.weak_count = inner.weak.count as _;
    }

    pub(crate) fn populate_debug_info(
        &self,
        out: &mut BinderNodeDebugInfo,
        guard: &Guard<'_, ProcessInner, SpinLockBackend>,
    ) {
        out.ptr = self.ptr as _;
        out.cookie = self.cookie as _;
        let inner = self.inner.access(guard);
        if inner.strong.has_count {
            out.has_strong_ref = 1;
        }
        if inner.weak.has_count {
            out.has_weak_ref = 1;
        }
    }

    pub(crate) fn force_has_count(&self, guard: &mut Guard<'_, ProcessInner, SpinLockBackend>) {
        let inner = self.inner.access_mut(guard);
        inner.strong.has_count = true;
        inner.weak.has_count = true;
    }

    fn write(&self, writer: &mut UserSlicePtrWriter, code: u32) -> Result {
        writer.write(&code)?;
        writer.write(&self.ptr)?;
        writer.write(&self.cookie)?;
        Ok(())
    }

    pub(crate) fn submit_oneway(
        &self,
        transaction: Arc<Transaction>,
        guard: &mut Guard<'_, ProcessInner, SpinLockBackend>,
    ) -> BinderResult {
        if guard.is_dead {
            return Err(BinderError::new_dead());
        }

        let inner = self.inner.access_mut(guard);
        if inner.has_pending_oneway_todo {
            inner.oneway_todo.push_back(transaction);
        } else {
            inner.has_pending_oneway_todo = true;
            guard.push_work(transaction).map_err(|(err, _work)| err)?;
        }
        Ok(())
    }

    pub(crate) fn release(&self, guard: &mut Guard<'_, ProcessInner, SpinLockBackend>) {
        // Move every pending oneshot message to the process todolist. The process
        // will cancel it later.
        //
        // New items can't be pushed after this call, since `submit_oneway` fails when the process
        // is dead, which is set before `Node::release` is called.
        //
        // TODO: Give our linked list implementation the ability to move everything in one go.
        while let Some(work) = self.inner.access_mut(guard).oneway_todo.pop_front() {
            guard.push_work_for_release(work);
        }
    }

    pub(crate) fn pending_oneway_finished(&self) {
        let mut guard = self.owner.inner.lock();
        if guard.is_dead {
            // Cleanup will happen in `Process::deferred_release`.
            return;
        }

        let inner = self.inner.access_mut(&mut guard);

        let transaction = inner.oneway_todo.pop_front();
        inner.has_pending_oneway_todo = transaction.is_some();
        if let Some(transaction) = transaction {
            match guard.push_work(transaction) {
                Ok(()) => {}
                Err((_err, work)) => {
                    // Process is dead.
                    // This shouldn't happen due to the `is_dead` check, but if it does, just put
                    // the work item back into the list. Process cleanup will take care of it.
                    let inner = self.inner.access_mut(&mut guard);
                    inner.oneway_todo.push_back(work);
                }
            }
        }
    }
}

impl DeliverToRead for Node {
    fn do_work(self: Arc<Self>, _thread: &Thread, writer: &mut UserSlicePtrWriter) -> Result<bool> {
        let mut owner_inner = self.owner.inner.lock();
        let inner = self.inner.access_mut(&mut owner_inner);
        let strong = inner.strong.count > 0;
        let has_strong = inner.strong.has_count;
        let weak = strong || inner.weak.count > 0;
        let has_weak = inner.weak.has_count;

        if weak && !has_weak {
            inner.weak.has_count = true;
            inner.active_inc_refs += 1;
        }

        if strong && !has_strong {
            inner.strong.has_count = true;
            inner.active_inc_refs += 1;
        }

        let no_active_inc_refs = inner.active_inc_refs == 0;
        let should_drop_weak = no_active_inc_refs && (!weak && has_weak);
        let should_drop_strong = no_active_inc_refs && (!strong && has_strong);
        if should_drop_weak {
            inner.weak.has_count = false;
        }
        if should_drop_strong {
            inner.strong.has_count = false;
        }
        if no_active_inc_refs && !weak {
            // Remove the node if there are no references to it.
            owner_inner.remove_node(self.ptr);
        }
        drop(owner_inner);

        if weak && !has_weak {
            self.write(writer, BR_INCREFS)?;
        }
        if strong && !has_strong {
            self.write(writer, BR_ACQUIRE)?;
        }
        if should_drop_strong {
            self.write(writer, BR_RELEASE)?;
        }
        if should_drop_weak {
            self.write(writer, BR_DECREFS)?;
        }

        Ok(true)
    }

    fn get_links(&self) -> &Links<dyn DeliverToRead> {
        &self.links
    }

    fn should_sync_wakeup(&self) -> bool {
        false
    }
}

/// Represents something that holds one or more ref-counts to a `Node`.
///
/// Whenever process A holds a refcount to a node owned by a different process B, then process A
/// will store a `NodeRef` that refers to the `Node` in process B. When process A releases the
/// refcount, we destroy the NodeRef, which decrements the ref-count in process A.
///
/// This type is also used for some other cases. For example, a transaction allocation holds a
/// refcount on the target node, and this is implemented by storing a `NodeRef` in the allocation
/// so that the destructor of the allocation will drop a refcount of the `Node`.
pub(crate) struct NodeRef {
    pub(crate) node: Arc<Node>,
    /// How many times does this NodeRef hold a refcount on the Node?
    strong_node_count: usize,
    weak_node_count: usize,
    /// How many times does userspace hold a refcount on this NodeRef?
    strong_count: usize,
    weak_count: usize,
}

impl NodeRef {
    pub(crate) fn new(node: Arc<Node>, strong_count: usize, weak_count: usize) -> Self {
        Self {
            node,
            strong_node_count: strong_count,
            weak_node_count: weak_count,
            strong_count,
            weak_count,
        }
    }

    pub(crate) fn absorb(&mut self, mut other: Self) {
        assert!(
            Arc::ptr_eq(&self.node, &other.node),
            "absorb called with differing nodes"
        );
        self.strong_node_count += other.strong_node_count;
        self.weak_node_count += other.weak_node_count;
        self.strong_count += other.strong_count;
        self.weak_count += other.weak_count;
        other.strong_count = 0;
        other.weak_count = 0;
        other.strong_node_count = 0;
        other.weak_node_count = 0;
    }

    pub(crate) fn clone(&self, strong: bool) -> Result<NodeRef> {
        if strong && self.strong_count == 0 {
            return Err(EINVAL);
        }
        Ok(self
            .node
            .owner
            .inner
            .lock()
            .new_node_ref(self.node.clone(), strong, None))
    }

    /// Updates (increments or decrements) the number of references held against the node. If the
    /// count being updated transitions from 0 to 1 or from 1 to 0, the node is notified by having
    /// its `update_refcount` function called.
    ///
    /// Returns whether `self` should be removed (when both counts are zero).
    pub(crate) fn update(&mut self, inc: bool, strong: bool) -> bool {
        if strong && self.strong_count == 0 {
            return false;
        }
        let (count, node_count, other_count) = if strong {
            (
                &mut self.strong_count,
                &mut self.strong_node_count,
                self.weak_count,
            )
        } else {
            (
                &mut self.weak_count,
                &mut self.weak_node_count,
                self.strong_count,
            )
        };
        if inc {
            if *count == 0 {
                *node_count = 1;
                self.node.update_refcount(true, 1, strong);
            }
            *count += 1;
        } else {
            *count -= 1;
            if *count == 0 {
                self.node.update_refcount(false, *node_count, strong);
                *node_count = 0;
                return other_count == 0;
            }
        }
        false
    }
}

impl Drop for NodeRef {
    fn drop(&mut self) {
        if self.strong_node_count > 0 {
            self.node
                .update_refcount(false, self.strong_node_count, true);
        }
        if self.weak_node_count > 0 {
            self.node
                .update_refcount(false, self.weak_node_count, false);
        }
    }
}
