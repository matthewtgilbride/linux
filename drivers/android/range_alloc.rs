// SPDX-License-Identifier: GPL-2.0

use kernel::{
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

        let remove_next = match cursor.peek_next() {
            Some((_, next)) if next.state == DescriptorState::Free => {
                // Merge current with next
                self.free_tree.remove(&(next.size, next.offset));
                size += next.size;
                true
            },
            _ => false,
        };

        let (_, desc) = cursor.current();
        if remove_next {
            desc.size = size;
            // We already checked that a next node exists,
            // so next() will return it successfully.
            cursor = cursor.next().unwrap();
            // We know there are at least 2 nodes,
            // so we can remove one safely.
            cursor = cursor.remove_current().unwrap();
            let (key, _) = cursor.current();
            if key > &offset {
                // We walked to the right when removing.
                // Go back to the original position.
                cursor = cursor.prev().unwrap()
            }
        }

        match cursor.peek_prev() {
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
