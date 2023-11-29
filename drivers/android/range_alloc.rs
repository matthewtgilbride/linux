// SPDX-License-Identifier: GPL-2.0
use core::mem::MaybeUninit;

use kernel::{
    prelude::*,
    rbtree::{RBTree, RBTreeNode, RBTreeNodeReservation},
    task::Pid,
    xarray::{flags::LOCK_IRQ, XArray},
};

/// Keeps track of allocations in a process' mmap.
///
/// Each process has an mmap where the data for incoming transactions will be placed. This struct
/// keeps track of allocations made in the mmap. For each allocation, we store a descriptor that
/// has metadata related to the allocation. We also keep track of available free space.
pub(crate) struct RangeAllocator<T: 'static> {
    descriptors: Pin<Box<XArray<Box<Descriptor<T>>>>>,
    free_tree: RBTree<FreeKey, ()>,
    size: usize,
    free_oneway_space: usize,
    pub(crate) oneway_spam_detected: bool,
    pub(crate) perf_results: PerfResults,
}

const PAGE_SIZE: usize = kernel::bindings::PAGE_SIZE as usize;

/// Represents a range of pages that have just become completely free.
#[derive(Copy, Clone)]
pub(crate) struct FreedRange {
    pub(crate) start_page_idx: usize,
    pub(crate) end_page_idx: usize,
}

impl FreedRange {
    fn interior_pages(offset: usize, size: usize) -> FreedRange {
        FreedRange {
            // Divide round up
            start_page_idx: (offset + (PAGE_SIZE - 1)) / PAGE_SIZE,
            // Divide round down
            end_page_idx: (offset + size) / PAGE_SIZE,
        }
    }
}

impl<T> RangeAllocator<T> {
    pub(crate) fn new(size: usize) -> Result<Self> {
        let descriptors = Box::pin_init(XArray::<Box<Descriptor<T>>>::new(LOCK_IRQ))?;
        let desc = Box::try_new(Descriptor::new(0, None, size))?;
        descriptors.as_ref().set(0, desc)?;
        let mut free_tree = RBTree::new();
        free_tree.try_create_and_insert((size, 0), ())?;
        Ok(Self {
            free_oneway_space: size / 2,
            descriptors,
            free_tree,
            oneway_spam_detected: false,
            perf_results: PerfResults::new(),
            size,
        })
    }

    fn find_best_match(&mut self, size: usize) -> Option<usize> {
        let free_cursor = self.free_tree.cursor_lower_bound(&(size, 0))?;
        let ((_, offset), _) = free_cursor.current();
        Some(*offset)
    }

    /// Try to reserve a new buffer, using the provided allocation if necessary.
    pub(crate) fn reserve_new(
        &mut self,
        size: usize,
        is_oneway: bool,
        pid: Pid,
        alloc: ReserveNewBox<T>,
    ) -> Result<usize> {
        let stop_watch = StopWatch::start("reserve_new");

        // Compute new value of free_oneway_space, which is set only on success.
        let new_oneway_space = if is_oneway {
            match self.free_oneway_space.checked_sub(size) {
                Some(new_oneway_space) => new_oneway_space,
                None => return Err(ENOSPC),
            }
        } else {
            self.free_oneway_space
        };

        // Start detecting spammers once we have less than 20%
        // of async space left (which is less than 10% of total
        // buffer size).
        //
        // (This will short-circut, so `low_oneway_space` is
        // only called when necessary.)
        self.oneway_spam_detected =
            is_oneway && new_oneway_space < self.size / 10 && self.low_oneway_space(pid);

        let Some(offset) = self.find_best_match(size) else {
            pr_warn!("ENOSPC from range_alloc.reserve_new - size: {}", size);
            return Err(ENOSPC);
        };

        let (found_size, found_off, new_desc, free_tree_node) =
            self.descriptors.get_scoped(offset as u64, |desc| {
                let desc = desc.unwrap();
                let found_size = desc.size;
                let found_off = desc.offset;

                // In case we need to break up the descriptor
                let new_desc =
                    Descriptor::new(found_off + size, Some(found_off), found_size - size);
                let (new_desc, free_tree_node, desc_node_res) = alloc.initialize(new_desc);

                desc.state = Some(DescriptorState::new(is_oneway, pid, desc_node_res));
                desc.size = size;

                (found_size, found_off, new_desc, free_tree_node)
            });

        self.free_oneway_space = new_oneway_space;
        self.free_tree.remove(&(found_size, found_off));

        if found_size != size {
            self.descriptors
                .as_ref()
                .set(new_desc.offset as u64, new_desc)?;
            self.free_tree.insert(free_tree_node);
        }

        self.perf_results.add(stop_watch.stop());

        Ok(found_off)
    }

    pub(crate) fn reservation_abort(&mut self, offset: usize) -> Result<FreedRange> {
        let stop_watch = StopWatch::start("reservation_abort");

        let (prev_offset, next_offset, size, reservation) =
            self.descriptors
                .as_ref()
                .get_scoped(offset as u64, |desc| {
                    let Some(desc) = desc else {
                        pr_warn!(
                            "EINVAL from range_alloc.reservation_abort - offset: {}",
                            offset
                        );
                        return Err(EINVAL);
                    };

                    let reservation = desc.try_change_state(|state| match state {
                        Some(DescriptorState::Reserved(reservation)) => (None, Ok(reservation)),
                        None => {
                            pr_warn!(
                                "EINVAL from range_alloc.reservation_abort - offset: {}",
                                offset
                            );
                            (None, Err(EINVAL))
                        }
                        allocated => {
                            pr_warn!(
                                "EPERM from range_alloc.reservation_abort - offset: {}",
                                offset
                            );
                            (allocated, Err(EPERM))
                        }
                    })?;

                    let free_oneway_space_add = if reservation.is_oneway { desc.size } else { 0 };

                    self.free_oneway_space += free_oneway_space_add;

                    Ok((desc.prev_offset, desc.next_offset(), desc.size, reservation))
                })?;

        let mut size = size;
        let mut offset = offset;

        let mut freed_range = FreedRange::interior_pages(offset, size);
        // Compute how large the next free region needs to be to include one more page in
        // the newly freed range.
        let add_next_page_needed = match (offset + size) % PAGE_SIZE {
            0 => usize::MAX,
            unalign => PAGE_SIZE - unalign,
        };
        // Compute how large the previous free region needs to be to include one more page
        // in the newly freed range.
        let add_prev_page_needed = match offset % PAGE_SIZE {
            0 => usize::MAX,
            unalign => unalign,
        };

        // Merge next into current if next is free
        let remove_next =
            self.descriptors
                .as_ref()
                .get_scoped(next_offset as u64, |next| match next {
                    Some(next) if next.state.is_none() => {
                        if next.size >= add_next_page_needed {
                            freed_range.end_page_idx += 1;
                        }
                        self.free_tree.remove(&(next.size, next.offset));
                        size += next.size;
                        true
                    }
                    _ => false,
                });

        if remove_next {
            // update current size with new size
            self.descriptors.as_ref().get_scoped(offset as u64, |desc| {
                if let Some(desc) = desc {
                    desc.size = size;
                }
            });
            // remove next
            self.descriptors.as_ref().remove(next_offset as u64);
        }

        // Merge current into prev if prev is free
        let remove_current = if let Some(prev_offset) = prev_offset {
            self.descriptors
                .as_ref()
                .get_scoped(prev_offset as u64, |prev| match prev {
                    Some(prev) if prev.state.is_none() => {
                        if prev.size >= add_prev_page_needed {
                            freed_range.start_page_idx -= 1;
                        }
                        self.free_tree.remove(&(prev.size, prev.offset));
                        let result = Some(offset);
                        size += prev.size;
                        // returned offset is now previous offset
                        offset = prev.offset;
                        // update prev size with new size
                        prev.size = size;
                        result
                    }
                    _ => None,
                })
        } else {
            None
        };

        // remove current if prev was free
        if let Some(remove_current) = remove_current {
            self.descriptors.as_ref().remove(remove_current as u64);
        };

        self.free_tree
            .insert(reservation.free_res.into_node((size, offset), ()));

        self.perf_results.add(stop_watch.stop());

        Ok(freed_range)
    }

    pub(crate) fn reservation_commit(&mut self, offset: usize, data: Option<T>) -> Result {
        let stop_watch = StopWatch::start("reservation_commit");
        
        self.descriptors.as_ref().get_scoped(offset as u64, |desc| {
            let Some(desc) = desc else {
                    pr_warn!(
                        "ENOENT from range_alloc.reservation_commit - offset: {}",
                        offset
                    );
                    return Err(ENOENT);
                };

            desc.try_change_state(|state| match state {
                Some(DescriptorState::Reserved(reservation)) => (
                    Some(DescriptorState::Allocated(reservation.allocate(data))),
                    Ok(()),
                ),
                other => {
                    pr_warn!(
                        "ENOENT from range_alloc.reservation_commit - offset: {}",
                        offset
                    );
                    (other, Err(ENOENT))
                }
            })
        })?;

        self.perf_results.add(stop_watch.stop());

        Ok(())
    }

    /// Takes an entry at the given offset from [`DescriptorState::Allocated`] to
    /// [`DescriptorState::Reserved`].
    ///
    /// Returns the size of the existing entry and the data associated with it.
    pub(crate) fn reserve_existing(&mut self, offset: usize) -> Result<(usize, Option<T>)> {
        let stop_watch = StopWatch::start("reserve_existing");
        
        let result = self.descriptors.as_ref().get_scoped(offset as u64, |desc| {
            let Some(desc) = desc else {
                    pr_warn!(
                        "ENOENT from range_alloc.reserve_existing - offset: {}",
                        offset
                    );
                    return Err(ENOENT)
                };

            let data = desc.try_change_state(|state| match state {
                Some(DescriptorState::Allocated(allocation)) => {
                    let (reservation, data) = allocation.deallocate();
                    (Some(DescriptorState::Reserved(reservation)), Ok(data))
                }
                other => {
                    pr_warn!(
                        "ENOENT from range_alloc.reserve_existing - offset: {}",
                        offset
                    );
                    (other, Err(ENOENT))
                }
            })?;

            Ok((desc.size, data))
        })?;

        self.perf_results.add(stop_watch.stop());

        Ok(result)
    }

    /// Call the provided callback at every allocated region.
    ///
    /// This destroys the range allocator. Used only during shutdown.
    pub(crate) fn take_for_each<F: Fn(usize, usize, Option<T>)>(&mut self, callback: F) {
        let mut index = 0;
        while let Some(new_index) = self.descriptors.find(index) {
            self.descriptors.get_scoped(new_index, |desc| {
                if let Some(desc) = desc {
                    if let Some(state) = &mut desc.state {
                        if let DescriptorState::Allocated(ref mut allocation) = state {
                            callback(desc.offset, desc.size, allocation.take());
                        }
                    }
                }
            });
            index = new_index + 1;
        }
    }

    /// Find the amount and size of buffers allocated by the current caller.
    ///
    /// The idea is that once we cross the threshold, whoever is responsible
    /// for the low async space is likely to try to send another async transaction,
    /// and at some point we'll catch them in the act.  This is more efficient
    /// than keeping a map per pid.
    fn low_oneway_space(&self, calling_pid: Pid) -> bool {
        let mut total_alloc_size = 0;
        let mut num_buffers = 0;
        let mut index = 0;
        while let Some(new_index) = self.descriptors.find(index) {
            self.descriptors.get_scoped(new_index, |desc| {
                if let Some(desc) = desc {
                    if let Some(state) = &desc.state {
                        if state.is_oneway() && state.pid() == calling_pid {
                            total_alloc_size += desc.size;
                            num_buffers += 1;
                        }
                    }
                }
            });
            index = new_index + 1;
        }

        // Warn if this pid has more than 50 transactions, or more than 50% of
        // async space (which is 25% of total buffer size). Oneway spam is only
        // detected when the threshold is exceeded.
        num_buffers > 50 || total_alloc_size > self.size / 4
    }

    #[allow(dead_code)]
    pub(crate) fn record_perf(&mut self, data: Box<[StopWatchResult; 100000]>) {
        self.perf_results.data = Some(data);
    }
}

struct Descriptor<T> {
    size: usize,
    offset: usize,
    prev_offset: Option<usize>,
    state: Option<DescriptorState<T>>,
}

impl<T> Descriptor<T> {
    fn new(offset: usize, prev_offset: Option<usize>, size: usize) -> Self {
        Self {
            size,
            offset,
            prev_offset,
            state: None,
        }
    }

    fn next_offset(&self) -> usize {
        self.size + self.offset
    }

    fn try_change_state<F, Data>(&mut self, f: F) -> Result<Data>
    where
        F: FnOnce(Option<DescriptorState<T>>) -> (Option<DescriptorState<T>>, Result<Data>),
    {
        let (new_state, result) = f(self.state.take());
        self.state = new_state;
        result
    }
}

enum DescriptorState<T> {
    Reserved(Reservation),
    Allocated(Allocation<T>),
}

impl<T> DescriptorState<T> {
    fn new(is_oneway: bool, pid: Pid, free_res: FreeNodeRes) -> Self {
        DescriptorState::Reserved(Reservation {
            is_oneway,
            pid,
            free_res,
        })
    }

    fn pid(&self) -> Pid {
        match self {
            DescriptorState::Reserved(inner) => inner.pid,
            DescriptorState::Allocated(inner) => inner.pid,
        }
    }

    fn is_oneway(&self) -> bool {
        match self {
            DescriptorState::Reserved(inner) => inner.is_oneway,
            DescriptorState::Allocated(inner) => inner.is_oneway,
        }
    }
}

struct Reservation {
    is_oneway: bool,
    pid: Pid,
    free_res: FreeNodeRes,
}

impl Reservation {
    fn allocate<T>(self, data: Option<T>) -> Allocation<T> {
        Allocation {
            data,
            is_oneway: self.is_oneway,
            pid: self.pid,
            free_res: self.free_res,
        }
    }
}

struct Allocation<T> {
    is_oneway: bool,
    pid: Pid,
    free_res: FreeNodeRes,
    data: Option<T>,
}

impl<T> Allocation<T> {
    fn deallocate(self) -> (Reservation, Option<T>) {
        (
            Reservation {
                is_oneway: self.is_oneway,
                pid: self.pid,
                free_res: self.free_res,
            },
            self.data,
        )
    }

    fn take(&mut self) -> Option<T> {
        self.data.take()
    }
}

// (Descriptor.size, Descriptor.offset)
type FreeKey = (usize, usize);
type FreeNodeRes = RBTreeNodeReservation<FreeKey, ()>;

/// An allocation for use by `reserve_new`.
pub(crate) struct ReserveNewBox<T> {
    desc: Box<MaybeUninit<Descriptor<T>>>,
    free_tree_node_res: FreeNodeRes,
    desc_node_res: FreeNodeRes,
}

impl<T> ReserveNewBox<T> {
    pub(crate) fn try_new() -> Result<Self> {
        let desc = Box::try_new_uninit()?;
        let free_tree_node_res = RBTree::try_reserve_node()?;
        let desc_node_res = RBTree::try_reserve_node()?;
        Ok(Self {
            desc,
            free_tree_node_res,
            desc_node_res,
        })
    }

    fn initialize(
        self,
        desc: Descriptor<T>,
    ) -> (Box<Descriptor<T>>, RBTreeNode<FreeKey, ()>, FreeNodeRes) {
        let size = desc.size;
        let offset = desc.offset;
        (
            Box::write(self.desc, desc),
            self.free_tree_node_res.into_node((size, offset), ()),
            self.desc_node_res,
        )
    }
}

pub(crate) struct PerfResults {
    pub(crate) data: Option<Box<[StopWatchResult; 100000]>>,
    pub(crate) next: usize,
}

impl PerfResults {
    fn new() -> Self {
        Self {
            data: None,
            next: 0
        }
    }
    fn add(&mut self, result: StopWatchResult) {
        if let Some(ref mut data) = &mut self.data {
            if self.next < 100000 {
                data[self.next] = result;
                self.next += 1;
            }
        }
    }
}

struct StopWatch {
    tag: &'static str,
    start: i64
}

impl StopWatch {
    fn start(tag: &'static str) -> Self {
        Self {
            tag,
            start: unsafe { kernel::bindings::ktime_get() },
        }
    }

    fn stop(self) -> StopWatchResult {
        StopWatchResult::new(self)
    }
}

#[allow(dead_code)]
#[derive(Clone, Copy)]
pub(crate) struct StopWatchResult {
    pub(crate) tag: &'static str,
    pub(crate) start: i64,
    pub(crate) duration: i64,
}

impl StopWatchResult {
    fn new(start: StopWatch) -> Self {
        let StopWatch { tag, start } = start;
        Self {
            tag,
            start,
            duration: unsafe { kernel::bindings::ktime_get() } - start
        }
    }
}
