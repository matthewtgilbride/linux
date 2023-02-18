// SPDX-License-Identifier: GPL-2.0

use kernel::{
    macros::kunit_tests,
    prelude::*,
    rbtree::RBTree,
};

pub(crate) struct RangeAllocator<T> {
    tree: RBTree<usize, Descriptor<T>>,
    free_tree: RBTree<(usize, usize), usize>
}

#[derive(Debug, PartialEq, Eq)]
enum DescriptorState {
    Free,
    Reserved,
    Allocated,
}

impl<T> RangeAllocator<T> {
    pub(crate) fn new(size: usize) -> Result<Self> {
        let desc = Descriptor::new(0, size);
        let mut tree = RBTree::new();
        let mut free_tree = RBTree::new();
        tree.try_insert(0, desc)?;
        free_tree.try_insert((size, 0), 0)?;
        Ok(Self { tree, free_tree })
    }

    fn find_best_match(&mut self, size: usize) -> Option<&mut Descriptor<T>> {
        let best_match_key = self.free_tree.upper_bound(&(size, 0));
        best_match_key.and_then(|(_, offset)| {
            self.tree.get_mut(offset)
        })
    }

    pub(crate) fn reserve_new(&mut self, size: usize) -> Result<usize> {
        let (offset, new) = match self.find_best_match(size) {
            None => return Err(ENOMEM),
            Some(found) => {
                // TODO: how to not mutate until the below tries succeed
                found.state = DescriptorState::Reserved;
                if found.size != size {
                    let new = Descriptor::new(found.offset + size, found.size - size);
                    (found.offset, Some(new))
                } else {
                    (found.offset, None)
                }
            },
        };
        
        let success: Result<()> = match new { 
            Some(new) => {
                self.free_tree.try_insert((new.size, new.offset), new.offset)?;
                self.tree.try_insert(new.offset, new)?;
                Ok(())
            },
            None => Ok(())
        };

        // we mutated the found descriptor above, if something fails we need to put it back...right?
        if let Err(_) = success {
            if let Some(mutated) = self.tree.get_mut(&offset) {
                mutated.state = DescriptorState::Free;
            }
            // TODO: what error?
            return Err(EAGAIN)
        }

        self.free_tree.remove(&(size, offset));
        Ok(offset)
    }

    pub(crate) fn reservation_abort(&mut self, offset: usize) -> Result {
        let current = self.tree.get(&offset);
        let (new, remove_current_offset, remove_next_offset) = match current {
            None => return Err(EINVAL),
            Some(current) if current.state == DescriptorState::Free => return Err(EINVAL),
            Some(current) if current.state == DescriptorState::Allocated => return Err(EPERM),
            Some(current) => {
                let prev = self
                    .tree
                    .predecessor(&offset)
                    .filter(|(_, v)| v.state == DescriptorState::Free)
                    .map(|(_, v)| v);
                let next = self
                    .tree
                    .successor(&offset)
                    .filter(|(_, v)| v.state == DescriptorState::Free)
                    .map(|(_, v)| v);

                let mut offset = current.offset;
                let mut size = current.size;

                // merge with previous
                if let Some(p) = prev {
                    offset = p.offset;
                    size += p.size;
                }
                // merge with next
                if let Some(n) = next {
                    size += n.size;
                }

                (
                    Descriptor::<T>::new(offset, size),
                    // if we merged with previous, current needs to be removed
                    prev.map(|_| current.offset),
                    // if we merged with next, next needs to be removed
                    next.map(|n| n.offset),
                )
            }
        };

        self.tree.try_insert(new.offset, new)?;

        if let Some(offset) = remove_current_offset {
            self.tree.remove(&offset);
        }

        if let Some(offset) = remove_next_offset {
            self.tree.remove(&offset);
        }

        Ok(())
    }

    pub(crate) fn reservation_commit(&mut self, offset: usize, data: Option<T>) -> Result {
        let desc = self.tree.get_mut(&offset).unwrap();
        desc.state = DescriptorState::Allocated;
        desc.data = data;
        Ok(())
    }

    /// Takes an entry at the given offset from [`DescriptorState::Allocated`] to
    /// [`DescriptorState::Reserved`].
    ///
    /// Returns the size of the existing entry and the data associated with it.
    pub(crate) fn reserve_existing(&mut self, offset: usize) -> Result<(usize, Option<T>)> {
        let desc = self.tree.get_mut(&offset).unwrap();
        if desc.state != DescriptorState::Allocated {
            return Err(ENOENT);
        }
        desc.state = DescriptorState::Reserved;
        Ok((desc.size, desc.data.take()))
    }

    pub(crate) fn for_each<F: Fn(usize, usize, Option<T>)>(&mut self, callback: F) {
        for (_, desc) in self.tree.iter_mut() {
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

#[kunit_tests(rust_android_binder_driver_range_alloc)]
mod tests {
    #[test]
    fn test_hello_world() {
        assert_eq!(1, 1);
    }
}
