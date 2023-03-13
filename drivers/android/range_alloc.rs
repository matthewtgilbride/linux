// SPDX-License-Identifier: GPL-2.0

use core::ptr::NonNull;
use kernel::{
    linked_list::{CursorMut, GetLinks, Links, List},
    macros::kunit_tests,
    rbtree::{RBTree, RBTreeNode, RBTreeNodeReservation},
    prelude::*,
};

pub(crate) struct RangeAllocator<T> {
    tree: RBTree<usize, Descriptor<T>>,
    free_tree: RBTree<(usize, usize), ()>
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
        let mut cursor = self.free_tree.cursor_lower_bound(&(size, 0))?;
        let ((_, offset), _) = cursor.current();
        self.tree.get_mut(&offset)
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
        let size = found.size;
        let offset = found.offset;
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

        desc.state = DescriptorState::Free;

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

/// An allocation for use by `reserve_new`.
pub(crate) struct ReserveNewDescriptor<T> {
    tree_node_res: RBTreeNodeReservation<usize, Descriptor<T>>,
    free_tree_node_res: RBTreeNodeReservation<(usize, usize), ()>
}

impl<T> ReserveNewDescriptor<T> {
    pub(crate) fn try_new() -> Result<Self> {
        let tree_node = RBTree::try_reserve_node()?;
        let free_tree_node = RBTree::try_reserve_node()?;
        Ok(Self { tree_node_res: tree_node, free_tree_node_res: free_tree_node })
    }

    fn initialize(self, desc: Descriptor<T>) -> (RBTreeNode<usize, Descriptor<T>>, RBTreeNode<(usize, usize), ()>) {
        let size = desc.size;
        let offset = desc.offset;
        (
            self.tree_node_res.into_node(offset, desc),
            self.free_tree_node_res.into_node((size, offset), ())
        )
    }
}

#[kunit_tests(rust_android_binder_driver_range_alloc)]
mod tests {
    use core::iter::Iterator;

    use crate::range_alloc::RangeAllocator;
    use crate::range_alloc::ReserveNewDescriptor;
    use crate::range_alloc::Descriptor;
    use crate::range_alloc::DescriptorState;
    use kernel::rbtree::{RBTree, RBTreeCursor};
    use kernel::prelude::*;
    #[test]
    fn test_reserve_new() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Free];
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let offset = ra.reserve_new(4, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Free];
        assert_eq!(offset, 0);
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let offset = ra.reserve_new(5, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        assert_eq!(offset, 4);
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let offset = ra.reserve_new(1, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved];
        assert_eq!(offset, 9);
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let offset = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap());
        assert!(offset.is_err());
    }

    #[test]
    fn test_reserve_new_noalloc() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Free];
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let mut offset = ra.reserve_new(4, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Free];
        assert_eq!(offset, 0);
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        assert!(ra.reserve_new_noalloc(5).unwrap().is_none());
        expected = &[DescriptorState::Reserved, DescriptorState::Reserved];
        offset = ra.reserve_new_noalloc(6).unwrap().unwrap();
        assert_eq!(offset, 4);
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    #[test]
    fn test_reservation_abort_no_merge() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_middle).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    #[test]
    fn test_reservation_abort_merge_right() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        let offset_right = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_right).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    #[test]
    fn test_reservation_abort_merge_left() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        let offset_left = ra.reserve_new(2,  ReserveNewDescriptor::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_left).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_middle).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    #[test]
    fn test_reservation_abort_merge_both() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        let offset_left = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        let offset_right = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_left).unwrap();
        ra.reservation_abort(offset_right).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_middle).unwrap();
        expected = &[DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    #[test]
    fn test_reservation_commit() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        let offset_left = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        let offset_right = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_left).unwrap();
        ra.reservation_abort(offset_right).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_commit(offset_middle, Some(1)).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Allocated, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    #[test]
    fn test_reserve_existing() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        let offset_left = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();
        let offset_right = ra.reserve_new(2, ReserveNewDescriptor::try_new().unwrap()).unwrap();

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_left).unwrap();
        ra.reservation_abort(offset_right).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_commit(offset_middle, Some(1)).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Allocated, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reserve_existing(offset_middle).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    fn assert_invariant_and_state(cursor: RBTreeCursor<'_, usize, Descriptor<usize>>, free_tree: &RBTree<(usize, usize), ()>, expected: &[DescriptorState]) {
        let mut cursor = cursor;
        let mut index = 1;
        let (_, mut desc) = cursor.current();

        assert_eq!(expected[0], desc.state);

        // free descriptors should always have corresponding entries in the free tree
        if desc.state == DescriptorState::Free {
            assert!(free_tree.get(&(desc.size, desc.offset)).is_some());
        }

        let mut last = (desc.offset, desc.size, desc.state);
        let mut next = cursor.next();

        while let Some(mut n) = next {
            let (_, desc) = n.current();
            let (last_offset, last_size, last_state) = last;

            // adjacent free descriptors should always be merged together
            assert!(match (last_state, desc.state) {
                (DescriptorState::Free, DescriptorState::Free) => false,
                _ => true
            });

            assert_eq!(expected[index], desc.state);

            // any descriptor's offset should always be a function of it's predecessors offset + size
            assert_eq!(desc.offset, last_offset + last_size);

            // free descriptors should always have corresponding entries in the free tree
            if desc.state == DescriptorState::Free {
                assert!(free_tree.get(&(desc.size, desc.offset)).is_some());
            }


            last = (desc.offset, desc.size, desc.state);
            index += 1;
            next = n.next();
        }

        assert!(expected.len() == index);

        // the free tree should not have extra entries
        let mut expected_free_count = 0;
        expected.iter()
            .filter(|&e| e == &DescriptorState::Free)
            .for_each(|_| { expected_free_count += 1; });

        let mut actual_free_count = 0;
        free_tree.iter()
            .for_each(|_| { actual_free_count += 1; });

        assert_eq!(expected_free_count, actual_free_count);
    }
}
