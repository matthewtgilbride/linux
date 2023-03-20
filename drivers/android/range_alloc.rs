// SPDX-License-Identifier: GPL-2.0

use kernel::{
    rbtree::{RBTree, RBTreeNode, RBTreeNodeReservation},
    macros::kunit_tests,
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
        let free_cursor = self.free_tree.cursor_lower_bound(&(size, 0))?;
        let ((_, offset), _) = free_cursor.current();
        self.tree.get_mut(&offset)
    }

    /// Try to reserve a new buffer, using the provided allocation if necessary.
    pub(crate) fn reserve_new(&mut self, size: usize, alloc: ReserveNewBox<T>) -> Result<usize> {
        let (found_size, found_offset) = match self.find_best_match(size) {
            None => {
                pr_warn!("ENOMEM from range_alloc.reserve_new - size: {}", size);
                return Err(ENOMEM);
            },
            Some(desc) => {
                let found = (desc.size, desc.offset);
                desc.state = DescriptorState::Reserved;
                desc.size = size;
                found
            },
        };

        self.free_tree.remove(&(found_size, found_offset));

        if found_size != size {
            // We need to break up the descriptor
            let new_offset = found_offset + size;
            let new_size = found_size - size;
            let desc = Descriptor::new(new_offset, new_size);
            let (tree_node, free_tree_node) = alloc.initialize(desc);
            self.tree.insert(tree_node);
            self.free_tree.insert(free_tree_node);
        }

        Ok(found_offset)
    }

    /// Try to reserve a new buffer, but don't allocate more memory.
    ///
    /// If this returns `Ok(None)`, the caller should make an allocation and try again by calling
    /// `reserve_new`.
    pub(crate) fn reserve_new_noalloc(&mut self, size: usize) -> Result<Option<usize>> {
        let found = match self.find_best_match(size) {
            None => {
                pr_warn!("ENOMEM from range_alloc.reserve_new_noalloc - size: {}", size);
                return Err(ENOMEM);
            },
            Some(found) if found.size == size => found,
            _ => return Ok(None)
        };

        found.state = DescriptorState::Reserved;
        let size = found.size;
        let offset = found.offset;
        self.free_tree.remove(&(size, offset));
        Ok(Some(offset))
    }

    pub(crate) fn reservation_abort(&mut self, offset: usize) -> Result {
        let mut cursor = self.tree.cursor_lower_bound(&offset).ok_or(EINVAL)?;
        let (_, desc) = cursor.current_mut();
        match desc.state {
            DescriptorState::Free => {
                pr_warn!("EINVAL from range_alloc.reservation_abort - offset: {}", offset);
                return Err(EINVAL);
            }
            DescriptorState::Allocated => {
                pr_warn!("EPERM from range_alloc.reservation_abort - offset: {}", offset);
                return Err(EPERM);
            },
            DescriptorState::Reserved => {}
        }

        let mut size = desc.size;
        let mut offset = desc.offset;

        let free_tree_res = RBTree::try_reserve_node()?;

        desc.state = DescriptorState::Free;

        // Merge next into current if next is free
        let remove_next = match cursor.peek_next() {
            Some((_, next)) if next.state == DescriptorState::Free => {
                self.free_tree.remove(&(next.size, next.offset));
                size += next.size;
                true
            }
            _ => false,
        };
        if remove_next {
            let (_, desc) = cursor.current_mut();
            desc.size = size;
            cursor.remove_next();
        }

        // Merge current into prev if prev is free
        match cursor.peek_prev_mut() {
            Some((_, prev)) if prev.state == DescriptorState::Free => {
                // merge previous with current, remove current
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
            pr_warn!("ENOENT from range_alloc.reserve_existing - offset: {}", offset);
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
    data: Option<T>,
}

impl<T> Descriptor<T> {
    fn new(offset: usize, size: usize) -> Self {
        Self {
            size,
            offset,
            state: DescriptorState::Free,
            data: None,
        }
    }
}

/// An allocation for use by `reserve_new`.
pub(crate) struct ReserveNewBox<T> {
    tree_node_res: RBTreeNodeReservation<usize, Descriptor<T>>,
    free_tree_node_res: RBTreeNodeReservation<(usize, usize), ()>
}

impl<T> ReserveNewBox<T> {
    pub(crate) fn try_new() -> Result<Self> {
        let tree_node_res = RBTree::try_reserve_node()?;
        let free_tree_node_res = RBTree::try_reserve_node()?;
        Ok(Self { tree_node_res, free_tree_node_res })
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
    use crate::range_alloc::ReserveNewBox;
    use crate::range_alloc::Descriptor;
    use crate::range_alloc::DescriptorState;
    use kernel::rbtree::{RBTree, RBTreeCursor};
    use kernel::prelude::*;
    #[test]
    fn test_reserve_new() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Free];
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let offset = ra.reserve_new(4, ReserveNewBox::try_new().unwrap()).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Free];
        assert_eq!(offset, 0);
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let offset = ra.reserve_new(5, ReserveNewBox::try_new().unwrap()).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        assert_eq!(offset, 4);
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let offset = ra.reserve_new(1, ReserveNewBox::try_new().unwrap()).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved];
        assert_eq!(offset, 9);
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let offset = ra.reserve_new(2, ReserveNewBox::try_new().unwrap());
        assert!(offset.is_err());
    }

    #[test]
    fn test_reserve_new_noalloc() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Free];
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let mut offset = ra.reserve_new(4, ReserveNewBox::try_new().unwrap()).unwrap();
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
        ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_middle).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    #[test]
    fn test_reservation_abort_merge_right() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        let offset_right = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_right).unwrap();
        expected = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    #[test]
    fn test_reservation_abort_merge_left() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Reserved, DescriptorState::Free];
        let offset_left = ra.reserve_new(2,  ReserveNewBox::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();

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
        let offset_left = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        let offset_right = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();

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
        let offset_left = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        let offset_right = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();

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
        let offset_left = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        let offset_middle = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();
        let offset_right = ra.reserve_new(2, ReserveNewBox::try_new().unwrap()).unwrap();

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(offset_left).unwrap();
        ra.reservation_abort(offset_right).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_commit(offset_middle, Some(1)).unwrap();
        expected = &[DescriptorState::Free, DescriptorState::Allocated, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let existing = ra.reserve_existing(offset_middle).unwrap();
        assert_eq!(existing, (2, Some(1)));
        expected = &[DescriptorState::Free, DescriptorState::Reserved, DescriptorState::Free];

        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    #[test]
    fn test_end_to_end() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(1040384).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Free];
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        assert!(ra.reserve_new_noalloc(16).unwrap().is_none());

        let offset = ra.reserve_new(16, ReserveNewBox::try_new().unwrap()).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Reserved, DescriptorState::Free];
        assert_eq!(offset, 0);
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_commit(0, Some(1)).unwrap();
        expected = &[DescriptorState::Allocated, DescriptorState::Free];
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        let existing = ra.reserve_existing(offset).unwrap();
        assert_eq!(existing, (16, Some(1)));

        expected = &[DescriptorState::Reserved, DescriptorState::Free];
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);

        ra.reservation_abort(0).unwrap();
        expected = &[DescriptorState::Free];
        assert_invariant_and_state(ra.tree.cursor_front().unwrap(), &ra.free_tree, expected);
    }

    fn assert_invariant_and_state(cursor: RBTreeCursor<'_, usize, Descriptor<usize>>, free_tree: &RBTree<(usize, usize), ()>, expected: &[DescriptorState]) {
        let mut index = 1;
        let (key, desc) = cursor.current();

        assert_eq!(key, &desc.offset);
        assert_eq!(expected[0], desc.state);

        // free descriptors should always have corresponding entries in the free tree
        if desc.state == DescriptorState::Free {
            assert!(free_tree.get(&(desc.size, desc.offset)).is_some());
        }

        let mut last = (desc.offset, desc.size, desc.state);
        let mut next = cursor.move_next();

        while let Some(n) = next {
            let (key, desc) = n.current();
            let (last_offset, last_size, last_state) = last;

            assert_eq!(key, &desc.offset);
            assert_eq!(expected[index], desc.state);

            // adjacent free descriptors should always be merged together
            assert!(match (last_state, desc.state) {
                (DescriptorState::Free, DescriptorState::Free) => false,
                _ => true
            });

            // any descriptor's offset should always be a function of it's predecessors offset + size
            assert_eq!(desc.offset, last_offset + last_size);

            // free descriptors should always have corresponding entries in the free tree
            if desc.state == DescriptorState::Free {
                assert!(free_tree.get(&(desc.size, desc.offset)).is_some());
            }


            last = (desc.offset, desc.size, desc.state);
            index += 1;
            next = n.move_next();
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
