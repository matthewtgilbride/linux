// SPDX-License-Identifier: GPL-2.0

use core::ptr::NonNull;
use kernel::{
    linked_list::{CursorMut, GetLinks, Links, List},
    macros::kunit_tests,
    prelude::*,
};

pub(crate) struct RangeAllocator<T> {
    list: List<Box<Descriptor<T>>>,
}

#[derive(Debug, PartialEq, Eq)]
enum DescriptorState {
    Free,
    Reserved,
    Allocated,
}

impl<T> RangeAllocator<T> {
    pub(crate) fn new(size: usize) -> Result<Self> {
        let desc = Box::try_new(Descriptor::new(0, size))?;
        let mut list = List::new();
        list.push_back(desc);
        Ok(Self { list })
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

    pub(crate) fn reserve_new(&mut self, size: usize) -> Result<usize> {
        let desc_ptr = match self.find_best_match(size) {
            None => return Err(ENOMEM),
            Some(found) => found,
        };

        // SAFETY: We hold the only mutable reference to list, so it cannot have changed.
        let desc = unsafe { &mut *desc_ptr.as_ptr() };
        if desc.size == size {
            desc.state = DescriptorState::Reserved;
            return Ok(desc.offset);
        }

        // We need to break up the descriptor.
        let new = Box::try_new(Descriptor::new(desc.offset + size, desc.size - size))?;
        unsafe { self.list.insert_after(desc_ptr, new) };
        desc.state = DescriptorState::Reserved;
        desc.size = size;
        Ok(desc.offset)
    }

    fn free_with_cursor(cursor: &mut CursorMut<'_, Box<Descriptor<T>>>) -> Result {
        let mut size = match cursor.current() {
            None => return Err(EINVAL),
            Some(ref mut entry) => {
                match entry.state {
                    DescriptorState::Free => return Err(EINVAL),
                    DescriptorState::Allocated => return Err(EPERM),
                    DescriptorState::Reserved => {}
                }
                entry.state = DescriptorState::Free;
                entry.size
            }
        };

        // Try to merge with the next entry.
        if let Some(next) = cursor.peek_next() {
            if next.state == DescriptorState::Free {
                next.offset -= size;
                next.size += size;
                size = next.size;
                cursor.remove_current();
            }
        }

        // Try to merge with the previous entry.
        if let Some(prev) = cursor.peek_prev() {
            if prev.state == DescriptorState::Free {
                prev.size += size;
                cursor.remove_current();
            }
        }

        Ok(())
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

    pub(crate) fn reservation_abort(&mut self, offset: usize) -> Result {
        // TODO: The force case is currently O(n), but could be made O(1) with unsafe.
        let mut cursor = self.find_at_offset(offset).ok_or(EINVAL)?;
        Self::free_with_cursor(&mut cursor)
    }

    pub(crate) fn reservation_commit(&mut self, offset: usize, data: Option<T>) -> Result {
        // TODO: This is currently O(n), make it O(1).
        let mut cursor = self.find_at_offset(offset).ok_or(ENOENT)?;
        let desc = cursor.current().unwrap();
        desc.state = DescriptorState::Allocated;
        desc.data = data;
        Ok(())
    }

    /// Takes an entry at the given offset from [`DescriptorState::Allocated`] to
    /// [`DescriptorState::Reserved`].
    ///
    /// Returns the size of the existing entry and the data associated with it.
    pub(crate) fn reserve_existing(&mut self, offset: usize) -> Result<(usize, Option<T>)> {
        // TODO: This is currently O(n), make it O(log n).
        let mut cursor = self.find_at_offset(offset).ok_or(ENOENT)?;
        let desc = cursor.current().unwrap();
        if desc.state != DescriptorState::Allocated {
            return Err(ENOENT);
        }
        desc.state = DescriptorState::Reserved;
        Ok((desc.size, desc.data.take()))
    }

    pub(crate) fn for_each<F: Fn(usize, usize, Option<T>)>(&mut self, callback: F) {
        let mut cursor = self.list.cursor_front_mut();
        while let Some(desc) = cursor.current() {
            if desc.state == DescriptorState::Allocated {
                callback(desc.offset, desc.size, desc.data.take());
            }

            cursor.move_next();
        }
    }
}

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

#[kunit_tests(rust_android_binder_driver_range_alloc)]
mod tests {
    use crate::range_alloc::RangeAllocator;
    use crate::range_alloc::Descriptor;
    use crate::range_alloc::DescriptorState;
    use kernel::linked_list::Cursor;
    use kernel::prelude::*;
    #[test]
    fn test_reserve_new() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected = [Some(DescriptorState::Free), None, None, None];
        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());
        let offset = ra.reserve_new(4).unwrap();
        expected = [Some(DescriptorState::Reserved), Some(DescriptorState::Free), None, None];
        assert_eq!(offset, 0);
        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());
        let offset = ra.reserve_new(5).unwrap();
        expected = [Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Free), None];
        assert_eq!(offset, 4);
        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());
        let offset = ra.reserve_new(1).unwrap();
        expected = [Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), None];
        assert_eq!(offset, 9);
        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());
        let offset = ra.reserve_new(2);
        assert!(offset.is_err());
    }

    #[test]
    fn test_reservation_abort_no_merge() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected = [Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Free)];
        ra.reserve_new(2).unwrap();
        let offset_middle = ra.reserve_new(2).unwrap();
        ra.reserve_new(2).unwrap();

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());

        ra.reservation_abort(offset_middle).unwrap();
        expected = [Some(DescriptorState::Reserved), Some(DescriptorState::Free), Some(DescriptorState::Reserved), Some(DescriptorState::Free)];

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());
    }

    #[test]
    fn test_reservation_abort_merge_right() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected = [Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Free)];
        ra.reserve_new(2).unwrap();
        ra.reserve_new(2).unwrap();
        let offset_right = ra.reserve_new(2).unwrap();

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());

        ra.reservation_abort(offset_right).unwrap();
        expected = [Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Free), None];

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());
    }

    #[test]
    fn test_reservation_abort_merge_left() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected = [Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Free)];
        let offset_left = ra.reserve_new(2).unwrap();
        let offset_middle = ra.reserve_new(2).unwrap();
        ra.reserve_new(2).unwrap();

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());

        ra.reservation_abort(offset_left).unwrap();
        expected = [Some(DescriptorState::Free), Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Free)];

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());

        ra.reservation_abort(offset_middle).unwrap();
        expected = [Some(DescriptorState::Free), Some(DescriptorState::Reserved), Some(DescriptorState::Free), None];

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());
    }

    #[test]
    fn test_reservation_abort_merge_both() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected = [Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Reserved), Some(DescriptorState::Free)];
        let offset_left = ra.reserve_new(2).unwrap();
        let offset_middle = ra.reserve_new(2).unwrap();
        let offset_right = ra.reserve_new(2).unwrap();

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());

        ra.reservation_abort(offset_left).unwrap();
        ra.reservation_abort(offset_right).unwrap();
        expected = [Some(DescriptorState::Free), Some(DescriptorState::Reserved), Some(DescriptorState::Free), None];

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());

        ra.reservation_abort(offset_middle).unwrap();
        expected = [Some(DescriptorState::Free), None, None, None];

        assert!(check_invariant_and_state(ra.list.cursor_front(), expected).is_none());
    }

    fn check_invariant_and_state(cursor: Cursor<Box<Descriptor<usize>>>, expected: [Option<DescriptorState>; 4]) -> Option<&str> {
        let mut cursor = cursor;
        let mut last = None;
        let mut index = 0;
        while let Some(desc) = cursor.current() {
            if let Some((last_offset, last_size, last_state)) = last {
                if desc.offset != last_offset + last_size {
                    return Some("offset/size invariant violated!");
                }
                match (last_state, &desc.state) {
                    (&DescriptorState::Free, &DescriptorState::Free) => {
                        return Some("adjacent free descriptors invariant violated!")
                    },
                    _ => {}
                }
            }
            match expected[index] {
                None => return Some("more descriptors than expected!"),
                Some(ref expected_state) => {
                    if expected_state != &desc.state {
                        return Some("unexpected descriptor state!")
                    }
                }
            }
            last = Some((&desc.offset, &desc.size, &desc.state));
            index += 1;
            cursor.move_next();
        }
        while index < 4 {
            if expected[index].is_some() {
                return Some("more expected than descriptors!")
            }
            index += 1
        }
        None
    }
}
