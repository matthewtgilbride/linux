// SPDX-License-Identifier: GPL-2.0

use core::mem::MaybeUninit;
use core::ptr::NonNull;
use kernel::{
    linked_list::{CursorMut, GetLinks, Links, List},
    prelude::*,
    task::Pid,
};

/// Keeps track of allocations in a process' mmap.
///
/// Each process has an mmap where the data for incoming transactions will be placed. This struct
/// keeps track of allocations made in the mmap. For each allocation, we store a descriptor that
/// has metadata related to the allocation. We also keep track of available free space.
pub(crate) struct RangeAllocator<T> {
    size: usize,
    list: List<Box<Descriptor<T>>>,
    free_oneway_space: usize,
    pub(crate) oneway_spam_detected: bool,
}

#[derive(Debug, PartialEq, Eq)]
enum DescriptorState {
    /// This region of the mmap is free.
    Free,
    /// This region of the mmap is allocated to a transaction. This allocation currently has an
    /// active `Allocation` object, and the metadata is in the `Allocation` object.
    Reserved { is_oneway: bool, pid: Pid },
    /// This region of the mmap is allocated to a transaction. This allocation currently does not
    /// have an active `Allocation` object, and the metadata is stored in the `data` field.
    Allocated { is_oneway: bool, pid: Pid },
}

impl DescriptorState {
    fn is_allocated(&self) -> bool {
        match self {
            DescriptorState::Allocated { .. } => true,
            _ => false,
        }
    }
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
        let desc = Box::try_new(Descriptor::new(0, size))?;
        let mut list = List::new();
        list.push_back(desc);
        Ok(Self {
            free_oneway_space: size / 2,
            oneway_spam_detected: false,
            size,
            list,
        })
    }

    fn find_best_match(&self, size: usize) -> Option<NonNull<Descriptor<T>>> {
        // TODO: Use a binary tree instead of list for this lookup.
        let mut best = None;
        let mut best_size = usize::MAX;
        let mut cursor = self.list.cursor_front();
        while let Some(desc) = cursor.current() {
            if desc.state == DescriptorState::Free {
                if size == desc.size {
                    return Some(NonNull::from(desc));
                }
                if size < desc.size && desc.size < best_size {
                    best = Some(NonNull::from(desc));
                    best_size = desc.size;
                }
            }
            cursor.move_next();
        }
        best
    }

    /// Try to reserve a new buffer, using the provided allocation if necessary.
    pub(crate) fn reserve_new(
        &mut self,
        size: usize,
        is_oneway: bool,
        pid: Pid,
        alloc: ReserveNewBox<T>,
    ) -> Result<(usize, AllocPtr<T>)> {
        // Compute new value of free_oneway_space, which is set only on success.
        let new_oneway_space = if is_oneway {
            match self.free_oneway_space.checked_sub(size) {
                Some(new_oneway_space) => new_oneway_space,
                None => return Err(ENOSPC),
            }
        } else {
            self.free_oneway_space
        };

        let desc_ptr = match self.find_best_match(size) {
            None => return Err(ENOSPC),
            Some(found) => found,
        };
        self.free_oneway_space = new_oneway_space;

        // Start detecting spammers once we have less than 20%
        // of async space left (which is less than 10% of total
        // buffer size).
        //
        // (This will short-circut, so `low_oneway_space` is
        // only called when necessary.)
        self.oneway_spam_detected =
            is_oneway && new_oneway_space < self.size / 10 && self.low_oneway_space(pid);

        // SAFETY: We hold the only mutable reference to list, so it cannot have changed.
        let desc = unsafe { &mut *desc_ptr.as_ptr() };
        desc.state = DescriptorState::Reserved { is_oneway, pid };

        if desc.size != size {
            // We need to break up the descriptor.
            let new_offset = desc.offset + size;
            let new_size = desc.size - size;
            desc.size = size;

            let new = alloc.initialize(Descriptor::new(new_offset, new_size));
            // SAFETY: The pointer points into the right list.
            unsafe { self.list.insert_after(desc_ptr, new) };
        }

        Ok((desc.offset, AllocPtr { ptr: desc_ptr }))
    }

    /// Free the provided allocation, then merge adjacent free regions if necessary.
    ///
    /// Returns how much to increase `free_oneway_space` by.
    fn free_with_cursor(
        cursor: &mut CursorMut<'_, Box<Descriptor<T>>>,
    ) -> Result<(usize, FreedRange)> {
        let mut freed_range;
        let add_next_page_needed;
        let add_prev_page_needed;
        let (mut size, is_oneway) = match cursor.current() {
            None => return Err(EINVAL),
            Some(ref mut entry) => {
                let is_oneway = match entry.state {
                    DescriptorState::Free => return Err(EINVAL),
                    DescriptorState::Allocated { .. } => return Err(EPERM),
                    DescriptorState::Reserved { is_oneway, .. } => is_oneway,
                };
                entry.state = DescriptorState::Free;

                freed_range = FreedRange::interior_pages(entry.offset, entry.size);
                // Compute how large the next free region needs to be to include one more page in
                // the newly freed range.
                add_next_page_needed = match (entry.offset + entry.size) % PAGE_SIZE {
                    0 => usize::MAX,
                    unalign => PAGE_SIZE - unalign,
                };
                // Compute how large the previous free region needs to be to include one more page
                // in the newly freed range.
                add_prev_page_needed = match entry.offset % PAGE_SIZE {
                    0 => usize::MAX,
                    unalign => unalign,
                };

                (entry.size, is_oneway)
            }
        };

        let free_oneway_space_add = if is_oneway { size } else { 0 };
        // Try to merge with the next entry.
        if let Some(next) = cursor.peek_next() {
            if next.state == DescriptorState::Free {
                if next.size >= add_next_page_needed {
                    freed_range.end_page_idx += 1;
                }

                next.offset -= size;
                next.size += size;
                size = next.size;
                cursor.remove_current();
            }
        }
        // Try to merge with the previous entry.
        if let Some(prev) = cursor.peek_prev() {
            if prev.state == DescriptorState::Free {
                if prev.size >= add_prev_page_needed {
                    freed_range.start_page_idx -= 1;
                }

                prev.size += size;
                cursor.remove_current();
            }
        }
        Ok((free_oneway_space_add, freed_range))
    }

    fn find_at_offset(&mut self, offset: usize) -> Option<CursorMut<'_, Box<Descriptor<T>>>> {
        let mut cursor = self.list.cursor_front_mut();
        while let Some(desc) = cursor.current() {
            if desc.offset == offset {
                return Some(cursor);
            }
            if desc.offset > offset {
                return None;
            }
            cursor.move_next();
        }
        None
    }

    pub(crate) fn reservation_abort(&mut self, offset: usize) -> Result<FreedRange> {
        let mut cursor = self.find_at_offset(offset).ok_or(EINVAL)?;
        let (free_oneway_space_add, freed_range) = Self::free_with_cursor(&mut cursor)?;
        self.free_oneway_space += free_oneway_space_add;
        Ok(freed_range)
    }

    pub(crate) fn reservation_commit(&mut self, ptr: AllocPtr<T>, data: Option<T>) -> Result {
        // SAFETY: We hold the lock, so we can access it.
        let desc = unsafe { &mut *(ptr.ptr.as_ptr()) };
        let (is_oneway, pid) = match desc.state {
            DescriptorState::Reserved { is_oneway, pid } => (is_oneway, pid),
            _ => return Err(ENOENT),
        };
        desc.state = DescriptorState::Allocated { is_oneway, pid };
        desc.data = data;
        Ok(())
    }

    /// Takes an entry at the given offset from [`DescriptorState::Allocated`] to
    /// [`DescriptorState::Reserved`].
    ///
    /// Returns the size of the existing entry and the data associated with it.
    pub(crate) fn reserve_existing(&mut self, offset: usize) -> Result<(usize, AllocPtr<T>, Option<T>)> {
        let mut cursor = self.find_at_offset(offset).ok_or(ENOENT)?;
        let desc = cursor.current().unwrap();
        let desc_ptr = AllocPtr { ptr: desc.into() };
        let (is_oneway, pid) = match desc.state {
            DescriptorState::Allocated { is_oneway, pid } => (is_oneway, pid),
            _ => return Err(ENOENT),
        };
        desc.state = DescriptorState::Reserved { is_oneway, pid };
        Ok((desc.size, desc_ptr, desc.data.take()))
    }

    /// Call the provided callback at every allocated region.
    ///
    /// This destroys the range allocator. Used only during shutdown.
    pub(crate) fn take_for_each<F: Fn(usize, usize, AllocPtr<T>, Option<T>)>(&mut self, callback: F) {
        let mut cursor = self.list.cursor_front_mut();
        while let Some(desc) = cursor.current() {
            let desc_ptr = AllocPtr { ptr: desc.into() };
            if desc.state.is_allocated() {
                callback(desc.offset, desc.size, desc_ptr, desc.data.take());
            }
            cursor.move_next();
        }
    }

    /// Find the amount and size of buffers allocated by the current caller.
    ///
    /// The idea is that once we cross the threshold, whoever is responsible
    /// for the low async space is likely to try to send another async transaction,
    /// and at some point we'll catch them in the act.  This is more efficient
    /// than keeping a map per pid.
    fn low_oneway_space(&self, calling_pid: Pid) -> bool {
        let mut cursor = self.list.cursor_front();
        let mut total_alloc_size = 0;
        let mut num_buffers = 0;
        while let Some(desc) = cursor.current() {
            match desc.state {
                DescriptorState::Reserved { is_oneway, pid }
                | DescriptorState::Allocated { is_oneway, pid } => {
                    if is_oneway && pid == calling_pid {
                        total_alloc_size = total_alloc_size + desc.size;
                        num_buffers += 1;
                    }
                }
                _ => {}
            }
            cursor.move_next();
        }

        // Warn if this pid has more than 50 transactions, or more than 50% of
        // async space (which is 25% of total buffer size). Oneway spam is only
        // detected when the threshold is exceeded.
        num_buffers > 50 || total_alloc_size > self.size / 4
    }
}

pub(crate) struct AllocPtr<T> {
    ptr: NonNull<Descriptor<T>>,
}

impl<T> Copy for AllocPtr<T> {}
impl<T> Clone for AllocPtr<T> {
    fn clone(&self) -> Self {
        Self { ptr: self.ptr }
    }
}

unsafe impl<T: Send + Sync> Send for AllocPtr<T> {}
unsafe impl<T: Send + Sync> Sync for AllocPtr<T> {}

struct Descriptor<T> {
    state: DescriptorState,
    size: usize,
    offset: usize,
    links: Links<Descriptor<T>>,
    data: Option<T>,
}

impl<T> Descriptor<T> {
    fn new(offset: usize, size: usize) -> Self {
        Self {
            size,
            offset,
            state: DescriptorState::Free,
            links: Links::new(),
            data: None,
        }
    }
}

impl<T> GetLinks for Descriptor<T> {
    type EntryType = Self;
    fn get_links(desc: &Self) -> &Links<Self> {
        &desc.links
    }
}

/// An allocation for use by `reserve_new`.
pub(crate) struct ReserveNewBox<T> {
    inner: Box<MaybeUninit<Descriptor<T>>>,
}

impl<T> ReserveNewBox<T> {
    pub(crate) fn try_new() -> Result<Self> {
        Ok(Self {
            inner: Box::try_new_uninit()?,
        })
    }

    fn initialize(self, desc: Descriptor<T>) -> Box<Descriptor<T>> {
        // SAFETY: Since we are initializing the memory with a valid value, its ok to transmute the
        // box into an initialized one.
        //
        // This can just be `Box::write(self.inner, desc)` when that method is stabilized.
        unsafe {
            let inner = Box::into_raw(self.inner) as *mut Descriptor<T>;
            core::ptr::write(inner, desc);
            Box::from_raw(inner)
        }
    }
}
