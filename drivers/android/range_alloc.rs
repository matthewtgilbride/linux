// SPDX-License-Identifier: GPL-2.0

use kernel::{
    
    macros::kunit_tests,
    prelude::*,
    rbtree::{RBTree, RBTreeNode, RBTreeNodeReservation},
};

pub(crate) struct RangeAllocator<T> {
    tree: RBTree<usize, Descriptor<T>>,
    free_tree: RBTree<(usize, usize), ()>,
    free_oneway_space: usize,
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
enum DescriptorState {
    Free,
    Reserved { is_oneway: bool },
    Allocated { is_oneway: bool },
}

impl DescriptorState {
    fn is_allocated(&self) -> bool {
        match self {
            DescriptorState::Allocated { .. } => true,
            _ => false,
        }
    }
}

impl<T> RangeAllocator<T> {
    pub(crate) fn new(size: usize) -> Result<Self> {
        let mut tree = RBTree::new();
        tree.try_insert(0, Descriptor::new(0, size))?;
        let mut free_tree = RBTree::new();
        free_tree.try_insert((size, 0), ())?;
        Ok(Self {
            free_oneway_space: size / 2,
            tree,
            free_tree,
        })
    }

    fn find_best_match(&mut self, size: usize) -> Option<&mut Descriptor<T>> {
        let free_cursor = self.free_tree.cursor_lower_bound(&(size, 0))?;
        let ((_, offset), _) = free_cursor.current();
        self.tree.get_mut(&offset)
    }

    /// Try to reserve a new buffer, using the provided allocation if necessary.
    pub(crate) fn reserve_new(
        &mut self,
        size: usize,
        is_oneway: bool,
        alloc: ReserveNewBox<T>,
    ) -> Result<usize> {
        // Compute new value of free_oneway_space, which is set only on success.
        let new_oneway_space = if is_oneway {
            match self.free_oneway_space.checked_sub(size) {
                Some(new_oneway_space) => new_oneway_space,
                None => return Err(ENOSPC),
            }
        } else {
            self.free_oneway_space
        };

        let (found_size, found_offset) = match self.find_best_match(size) {
            None => {
                pr_warn!("ENOSPC from range_alloc.reserve_new - size: {}", size);
                return Err(ENOSPC);
            }
            Some(desc) => {
                let found = (desc.size, desc.offset);
                desc.state = DescriptorState::Reserved { is_oneway };
                desc.size = size;
                found
            }
        };

        self.free_oneway_space = new_oneway_space;
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
    pub(crate) fn reserve_new_noalloc(
        &mut self,
        size: usize,
        is_oneway: bool,
    ) -> Result<Option<usize>> {
        // Compute new value of free_oneway_space, which is set only on success.
        let new_oneway_space = if is_oneway {
            match self.free_oneway_space.checked_sub(size) {
                Some(new_oneway_space) => new_oneway_space,
                None => return Err(ENOSPC),
            }
        } else {
            self.free_oneway_space
        };

        let (found_size, found_offset) = match self.find_best_match(size) {
            None => {
                pr_warn!(
                    "ENOSPC from range_alloc.reserve_new_noalloc - size: {}",
                    size
                );
                return Err(ENOSPC);
            }
            Some(desc) if desc.size == size => {
                let found = (desc.size, desc.offset);
                desc.state = DescriptorState::Reserved { is_oneway };
                found
            }
            _ => return Ok(None),
        };

        self.free_oneway_space = new_oneway_space;
        self.free_tree.remove(&(found_size, found_offset));
        Ok(Some(found_offset))
    }

    pub(crate) fn reservation_abort(&mut self, offset: usize) -> Result {
        let mut cursor = self.tree.cursor_lower_bound(&offset).ok_or_else(|| {
            pr_warn!(
                "EINVAL from range_alloc.reservation_abort - offset: {}",
                offset
            );
            EINVAL
        })?;
        let (_, desc) = cursor.current_mut();
        let is_oneway = match desc.state {
            DescriptorState::Free => {
                pr_warn!(
                    "EINVAL from range_alloc.reservation_abort - offset: {}",
                    offset
                );
                return Err(EINVAL);
            }
            DescriptorState::Allocated { .. } => {
                pr_warn!(
                    "EPERM from range_alloc.reservation_abort - offset: {}",
                    offset
                );
                return Err(EPERM);
            }
            DescriptorState::Reserved { is_oneway } => is_oneway,
        };

        let mut size = desc.size;
        let mut offset = desc.offset;
        let free_oneway_space_add = if is_oneway { size } else { 0 };

        let free_tree_res = RBTree::try_reserve_node()?;

        self.free_oneway_space += free_oneway_space_add;

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
            }
            _ => {}
        };

        self.free_tree
            .insert(free_tree_res.into_node((size, offset), ()));

        Ok(())
    }

    pub(crate) fn reservation_commit(&mut self, offset: usize, data: Option<T>) -> Result {
        let mut desc = self.tree.get_mut(&offset).ok_or_else(|| {
            pr_warn!(
                "ENOENT from range_alloc.reservation_commit - offset: {}",
                offset
            );
            ENOENT
        })?;
        let is_oneway = match desc.state {
            DescriptorState::Reserved { is_oneway } => is_oneway,
            _ => {
                pr_warn!(
                    "ENOENT from range_alloc.reservation_commit - offset: {}",
                    offset
                );
                return Err(ENOENT);
            }
        };
        desc.state = DescriptorState::Allocated { is_oneway };
        desc.data = data;
        Ok(())
    }

    /// Takes an entry at the given offset from [`DescriptorState::Allocated`] to
    /// [`DescriptorState::Reserved`].
    ///
    /// Returns the size of the existing entry and the data associated with it.
    pub(crate) fn reserve_existing(&mut self, offset: usize) -> Result<(usize, Option<T>)> {
        let mut desc = self.tree.get_mut(&offset).ok_or_else(|| {
            pr_warn!(
                "ENOENT from range_alloc.reserve_existing - offset: {}",
                offset
            );
            ENOENT
        })?;
        let is_oneway = match desc.state {
            DescriptorState::Allocated { is_oneway } => is_oneway,
            _ => {
                pr_warn!(
                    "ENOENT from range_alloc.reserve_existing - offset: {}",
                    offset
                );
                return Err(ENOENT);
            }
        };
        desc.state = DescriptorState::Reserved { is_oneway };
        Ok((desc.size, desc.data.take()))
    }

    pub(crate) fn for_each<F: Fn(usize, usize, Option<T>)>(&mut self, callback: F) {
        let mut iter = self.tree.iter_mut();
        while let Some((_, desc)) = iter.next() {
            if desc.state.is_allocated() {
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
    free_tree_node_res: RBTreeNodeReservation<(usize, usize), ()>,
}

impl<T> ReserveNewBox<T> {
    pub(crate) fn try_new() -> Result<Self> {
        let tree_node_res = RBTree::try_reserve_node()?;
        let free_tree_node_res = RBTree::try_reserve_node()?;
        Ok(Self {
            tree_node_res,
            free_tree_node_res,
        })
    }

    fn initialize(
        self,
        desc: Descriptor<T>,
    ) -> (
        RBTreeNode<usize, Descriptor<T>>,
        RBTreeNode<(usize, usize), ()>,
    ) {
        let size = desc.size;
        let offset = desc.offset;
        (
            self.tree_node_res.into_node(offset, desc),
            self.free_tree_node_res.into_node((size, offset), ()),
        )
    }
}


#[kunit_tests(rust_android_binder_driver_range_alloc)]
mod tests {
    use core::iter::Iterator;

    use crate::range_alloc::Descriptor;
    use crate::range_alloc::DescriptorState;
    use crate::range_alloc::RangeAllocator;
    use crate::range_alloc::ReserveNewBox;
    use kernel::prelude::*;
    use kernel::rbtree::{RBTree, RBTreeCursor};
    #[test]
    fn test_reserve_new() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Free];
        assert_invariant_and_state(&mut ra, expected);

        let offset = ra
            .reserve_new(4, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        expected = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        assert_eq!(offset, 0);
        assert_invariant_and_state(&mut ra, expected);

        let offset = ra
            .reserve_new(5, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        expected = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        assert_eq!(offset, 4);
        assert_invariant_and_state(&mut ra, expected);

        let offset = ra
            .reserve_new(1, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        expected = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
        ];
        assert_eq!(offset, 9);
        assert_invariant_and_state(&mut ra, expected);

        let offset = ra.reserve_new(2, false, ReserveNewBox::try_new().unwrap());
        assert!(offset.is_err());
    }

    #[test]
    fn test_reserve_new_noalloc() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Free];
        assert_invariant_and_state(&mut ra, expected);

        let mut offset = ra
            .reserve_new(4, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        expected = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        assert_eq!(offset, 0);
        assert_invariant_and_state(&mut ra, expected);

        assert!(ra.reserve_new_noalloc(5, false).unwrap().is_none());
        expected = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
        ];
        offset = ra.reserve_new_noalloc(6, false).unwrap().unwrap();
        assert_eq!(offset, 4);
        assert_invariant_and_state(&mut ra, expected);
    }

    #[test]
    fn test_reservation_abort_no_merge() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        ra.reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let offset_middle = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        ra.reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(offset_middle).unwrap();
        expected = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);
    }

    #[test]
    fn test_reservation_abort_merge_right() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        ra.reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        ra.reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let offset_right = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(offset_right).unwrap();
        expected = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);
    }

    #[test]
    fn test_reservation_abort_merge_left() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        let offset_left = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let offset_middle = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        ra.reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(offset_left).unwrap();
        expected = &[
            DescriptorState::Free,
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(offset_middle).unwrap();
        expected = &[
            DescriptorState::Free,
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);
    }

    #[test]
    fn test_reservation_abort_merge_both() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        let offset_left = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let offset_middle = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let offset_right = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(offset_left).unwrap();
        ra.reservation_abort(offset_right).unwrap();
        expected = &[
            DescriptorState::Free,
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(offset_middle).unwrap();
        expected = &[DescriptorState::Free];

        assert_invariant_and_state(&mut ra, expected);
    }

    #[test]
    fn test_reservation_commit() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        let offset_left = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let offset_middle = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let offset_right = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(offset_left).unwrap();
        ra.reservation_abort(offset_right).unwrap();
        expected = &[
            DescriptorState::Free,
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_commit(offset_middle, Some(1)).unwrap();
        expected = &[
            DescriptorState::Free,
            DescriptorState::Allocated { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);
    }

    #[test]
    fn test_reserve_existing() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(10).unwrap();
        let mut expected: &[DescriptorState] = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        let offset_left = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let offset_middle = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let offset_right = ra
            .reserve_new(2, false, ReserveNewBox::try_new().unwrap())
            .unwrap();

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(offset_left).unwrap();
        ra.reservation_abort(offset_right).unwrap();
        expected = &[
            DescriptorState::Free,
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_commit(offset_middle, Some(1)).unwrap();
        expected = &[
            DescriptorState::Free,
            DescriptorState::Allocated { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);

        let existing = ra.reserve_existing(offset_middle).unwrap();
        assert_eq!(existing, (2, Some(1)));
        expected = &[
            DescriptorState::Free,
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];

        assert_invariant_and_state(&mut ra, expected);
    }

    #[test]
    fn test_end_to_end() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(1040384).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Free];
        assert_invariant_and_state(&mut ra, expected);

        assert!(ra.reserve_new_noalloc(16, false).unwrap().is_none());

        let offset = ra
            .reserve_new(16, false, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let mut expected: &[DescriptorState] = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        assert_eq!(offset, 0);
        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_commit(0, Some(1)).unwrap();
        expected = &[
            DescriptorState::Allocated { is_oneway: false },
            DescriptorState::Free,
        ];
        assert_invariant_and_state(&mut ra, expected);

        let existing = ra.reserve_existing(offset).unwrap();
        assert_eq!(existing, (16, Some(1)));

        expected = &[
            DescriptorState::Reserved { is_oneway: false },
            DescriptorState::Free,
        ];
        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(0).unwrap();
        expected = &[DescriptorState::Free];
        assert_invariant_and_state(&mut ra, expected);
    }

    #[test]
    fn test_end_to_end_oneway() {
        let mut ra: RangeAllocator<usize> = RangeAllocator::new(1040384).unwrap();
        let mut expected: &[DescriptorState] = &[DescriptorState::Free];
        assert_invariant_and_state(&mut ra, expected);

        assert!(ra.reserve_new_noalloc(16, true).unwrap().is_none());

        let offset = ra
            .reserve_new(16, true, ReserveNewBox::try_new().unwrap())
            .unwrap();
        let mut expected: &[DescriptorState] = &[
            DescriptorState::Reserved { is_oneway: true },
            DescriptorState::Free,
        ];
        assert_eq!(offset, 0);
        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_commit(0, Some(1)).unwrap();
        expected = &[
            DescriptorState::Allocated { is_oneway: true },
            DescriptorState::Free,
        ];
        assert_invariant_and_state(&mut ra, expected);

        let existing = ra.reserve_existing(offset).unwrap();
        assert_eq!(existing, (16, Some(1)));

        expected = &[
            DescriptorState::Reserved { is_oneway: true },
            DescriptorState::Free,
        ];
        assert_invariant_and_state(&mut ra, expected);

        let offset = ra
            .reserve_new(16, true, ReserveNewBox::try_new().unwrap())
            .unwrap();
        expected = &[
            DescriptorState::Reserved { is_oneway: true },
            DescriptorState::Reserved { is_oneway: true },
            DescriptorState::Free,
        ];
        assert_eq!(offset, 16);
        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_commit(offset, Some(1)).unwrap();
        expected = &[
            DescriptorState::Reserved { is_oneway: true },
            DescriptorState::Allocated { is_oneway: true },
            DescriptorState::Free,
        ];
        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_commit(0, Some(1)).unwrap();
        expected = &[
            DescriptorState::Allocated { is_oneway: true },
            DescriptorState::Allocated { is_oneway: true },
            DescriptorState::Free,
        ];
        assert_invariant_and_state(&mut ra, expected);

        let existing = ra.reserve_existing(0).unwrap();
        assert_eq!(existing, (16, Some(1)));

        expected = &[
            DescriptorState::Reserved { is_oneway: true },
            DescriptorState::Allocated { is_oneway: true },
            DescriptorState::Free,
        ];
        assert_invariant_and_state(&mut ra, expected);

        let existing = ra.reserve_existing(16).unwrap();
        assert_eq!(existing, (16, Some(1)));

        expected = &[
            DescriptorState::Reserved { is_oneway: true },
            DescriptorState::Reserved { is_oneway: true },
            DescriptorState::Free,
        ];
        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(0).unwrap();
        expected = &[
            DescriptorState::Free,
            DescriptorState::Reserved { is_oneway: true },
            DescriptorState::Free,
        ];
        assert_invariant_and_state(&mut ra, expected);

        ra.reservation_abort(16).unwrap();
        expected = &[DescriptorState::Free];
        assert_invariant_and_state(&mut ra, expected);
    }

    fn assert_invariant_and_state(ra: &mut RangeAllocator<usize>, expected: &[DescriptorState]) {
        let cursor: RBTreeCursor<'_, usize, Descriptor<usize>> = ra.tree.cursor_front().unwrap();
        let free_tree: &RBTree<(usize, usize), ()> = &ra.free_tree;
        let free_oneway_space = ra.free_oneway_space;

        let mut index = 1;
        let (key, desc) = cursor.current();

        assert_eq!(key, &desc.offset);
        assert_eq!(expected[0], desc.state);

        let mut total_space = desc.size;
        let mut consumed_oneway_space = 0;

        match desc.state {
            // free descriptors should always have corresponding entries in the free tree
            DescriptorState::Free => {
                assert!(free_tree.get(&(desc.size, desc.offset)).is_some());
            }
            // oneway descriptors consume oneway space
            DescriptorState::Reserved { is_oneway } if is_oneway => {
                consumed_oneway_space += desc.size;
            }
            DescriptorState::Allocated { is_oneway } if is_oneway => {
                consumed_oneway_space += desc.size;
            }
            _ => {}
        }

        let mut last = (desc.offset, desc.size, desc.state);
        let mut next = cursor.move_next();

        while let Some(n) = next {
            let (key, desc) = n.current();
            let (last_offset, last_size, last_state) = last;

            assert_eq!(key, &desc.offset);
            assert_eq!(expected[index], desc.state);

            total_space += desc.size;

            match desc.state {
                // free descriptors should always have corresponding entries in the free tree
                DescriptorState::Free => {
                    assert!(free_tree.get(&(desc.size, desc.offset)).is_some());
                }
                // oneway descriptors consume oneway space
                DescriptorState::Reserved { is_oneway } if is_oneway => {
                    consumed_oneway_space += desc.size;
                }
                DescriptorState::Allocated { is_oneway } if is_oneway => {
                    consumed_oneway_space += desc.size;
                }
                _ => {}
            }

            // any descriptor's offset should always be a function of it's predecessors offset + size
            assert_eq!(desc.offset, last_offset + last_size);

            // adjacent descriptors should never both be free (as they should have been merged)
            assert!((last_state, desc.state) != (DescriptorState::Free, DescriptorState::Free));

            last = (desc.offset, desc.size, desc.state);
            index += 1;
            next = n.move_next();
        }

        assert!(expected.len() == index);

        // free_oneway_space = (total_space / 2) - consumed_oneway_space
        assert_eq!(
            free_oneway_space,
            ((total_space / 2) - consumed_oneway_space)
        );

        // the free tree should not have extra entries
        let expected_free_count = expected
            .iter()
            .filter(|&e| e == &DescriptorState::Free)
            .count();

        let actual_free_count = free_tree.iter().count();

        assert_eq!(expected_free_count, actual_free_count);
    }
}
