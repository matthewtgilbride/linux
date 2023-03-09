// SPDX-License-Identifier: GPL-2.0

use core::ptr::NonNull;
use kernel::{
    linked_list::{CursorMut, GetLinks, Links, List},
    macros::kunit_tests,
    prelude::*,
};

pub(crate) struct RangeAllocator<T> {
    tree: RBTree<usize, Descriptor<T>>,
    free_tree: RBTree<(usize, usize), ()>
}

#[derive(Debug, PartialEq, Eq)]
enum DescriptorState {
    Free,
    Reserved,
    Allocated,
}

impl<T> RangeAllocator<T> {
    pub(crate) fn new(size: usize) -> Result<Self> {
        let mut tree = RBTree::new();
        tree.try_insert(0, Descriptor::new(0, size))?;
        let mut free_tree = RBTree::new();
        free_tree.try_insert((size, 0), ())?;
        Ok(Self { tree, free_tree })
    }

    fn find_best_match(&mut self, size: usize) -> Option<&mut Descriptor<T>> {
        let mut cursor = match self.free_tree.cursor_lower_bound(&(size, 0)) {
            None => return None,
            Some(cursor) => cursor
        };
        let ((_, offset), _) = cursor.current();
        self.tree.get_mut(&offset) // TODO: fighting the borrow checker
    }

    /// Try to reserve a new buffer, using the provided allocation if necessary.
    pub(crate) fn reserve_new(&mut self, size: usize, alloc: ReserveNewDescriptor<T>) -> Result<usize> {
        let (found_size, found_offset) = match self.find_best_match(size) {
            None => return Err(ENOMEM),
            Some(desc) => {
                let found = (desc.size, desc.offset);
                desc.state = DescriptorState::Reserved;
                desc.size = size;
                found
            },
        };

        self.free_tree.remove(&(found_size, found_offset));

        if found_size == size {
            return Ok(found_offset);
        }

        // We need to break up the descriptor
        let new_offset = found_offset + size;
        let new_size = found_size - size;
        let desc = Descriptor::new(new_offset, new_size);
        let (tree_node, free_tree_node) = alloc.initialize(desc);
        self.tree.insert(tree_node);
        self.free_tree.insert(free_tree_node);

        Ok(found_offset)
    }

    /// Try to reserve a new buffer, but don't allocate more memory.
    ///
    /// If this returns `Ok(None)`, the caller should make an allocation and try again by calling
    /// `reserve_new`.
    pub(crate) fn reserve_new_noalloc(&mut self, size: usize) -> Result<Option<usize>> {
        let found = match self.find_best_match(size) {
            None => return Err(ENOMEM),
            Some(found) => {
                if found.size != size {
                    return Ok(None);
                }
                found
            }
        };

        found.state = DescriptorState::Reserved;
        let size = found.size; // why do I have to have these let statements
        let offset = found.offset; // to make you happy, borrow checker?
        self.free_tree.remove(&(size, offset));
        Ok(Some(offset))
    }

    pub(crate) fn reservation_abort(&mut self, offset: usize) -> Result {
        let mut cursor = self.tree.cursor_lower_bound(&offset).ok_or(EINVAL)?;
        let (_, desc) = cursor.current();
        match desc.state {
            DescriptorState::Free => return Err(EINVAL),
            DescriptorState::Allocated => return Err(EPERM),
            DescriptorState::Reserved => {}
        }

        let mut size = desc.size;
        let mut offset = desc.offset;

        let free_tree_res = RBTree::try_reserve_node()?;

        match cursor.peek_next() {
            Some((_, next)) if next.state == DescriptorState::Free => {
                // update next to be merged with current, remove current
                self.free_tree.remove(&(next.size, next.offset));
                size += next.size;
                next.size = size;
                next.offset = offset;
                // we already checked that a next node exists, remove_current
                // will return it successfully
                cursor = cursor.remove_current().unwrap();
            }
            _ => {}, 
        };

        match cursor.peek_prev() {
            Some((_, prev)) if prev.state == DescriptorState::Free => {
                // update previous to be merged with current, remove current
                self.free_tree.remove(&(prev.size, prev.offset));
                offset = prev.offset;
                size += prev.size;
                prev.size = size;
                cursor.remove_current();
            },
            _ => {}
        };

        self.free_tree.insert(free_tree_res.into_node((size, offset), ()));
        
        Ok(())
    }

    pub(crate) fn reservation_commit(&mut self, offset: usize, data: Option<T>) -> Result {
        // TODO: the state of the found descriptor isn't checked.  Should it be? Should None be handled?
        let mut desc = self.tree.get_mut(&offset).unwrap();
        desc.state = DescriptorState::Allocated;
        desc.data = data;
        Ok(())
    }

    /// Takes an entry at the given offset from [`DescriptorState::Allocated`] to
    /// [`DescriptorState::Reserved`].
    ///
    /// Returns the size of the existing entry and the data associated with it.
    pub(crate) fn reserve_existing(&mut self, offset: usize) -> Result<(usize, Option<T>)> {
        let mut desc = self.tree.get_mut(&offset).ok_or(ENOENT)?;
        if desc.state != DescriptorState::Allocated {
            return Err(ENOENT);
        }
        desc.state = DescriptorState::Reserved;
        Ok((desc.size, desc.data.take()))
    }

    pub(crate) fn for_each<F: Fn(usize, usize, Option<T>)>(&mut self, callback: F) {
        let mut iter = self.tree.iter_mut();
        while let Some((_, desc)) = iter.next() {
            if desc.state == DescriptorState::Allocated {
                callback(desc.offset, desc.size, desc.data.take());
            }
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
