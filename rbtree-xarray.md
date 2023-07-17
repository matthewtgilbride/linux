Subject: Migrating from `RBTree` to `XArray` in Binder

# Background
Hello,

I'm working on a project to rewrite Android's
[binder driver](https://github.com/torvalds/linux/tree/master/drivers/android) in rust.
Recently we addressed some TODOs around worst-case performance by
[using red-black trees instead of a linked list](https://android-review.googlesource.com/c/kernel/common/+/2567935).
A rudimentary benchmark showed that worst case performance of the related code was better in practice:

| Duration (μs)| RBTree    | LinkedList |
| ------------ | --------- | ---------- |
| 0-9,999      | 8,076,424 | 7,533,262  |
| 10k-20k      | 40        | 520        |
| 20k-30k      | 7         | 49         |
| 30k-40k      | 2         | 9          |
| 40k-50k      | 0         | 1          |
| 50k-60k      | 0         | 0          |
| 60k-         | 1         | 0          |
| Total        | 8,076,474 | 7,533,841  |

We've since learned that the upstream `RBTree` data structure is deprecated.  Our understanding is that `RBTree` should
never be used for any new code, and we should use the `XArray` data structure instead.

`XArray` should be fine for all of our use cases in binder except this one - the "range allocator".
We're not sure what to do here, and are looking for guidance.  [The C driver uses
RBTree](https://github.com/torvalds/linux/blob/3f01e9fed8454dcd89727016c3e5b2fbb8f8e50c/drivers/android/binder_alloc.h#L83-L85), 
which led us down this path in the first place.

## TLDR
**How should we use `XArray` (or some other data structure that is not deprecated) to address the following scenario?**

# Range Allocator
Range allocator stores collection of "Descriptors":
```
struct Descriptor<T> {
    size: usize,
    offset: usize,
    data: Option<T>,
    state: DescriptorState // Free, Reserved, or Allocated
}
```

## Lookups
We need to look descriptors up one of two ways:
1. Find a descriptor with a particular `offset`.  Each offset in the collection is unique.
2. Find the *smallest* descriptor with a state of `Free` and a `size` greater than or equal to a given `size`.  Multiple descriptors can have the same size.

## Merging
The other nuance is that neighboring descriptors (based on their `offset`) should never *both* be in a state of `Free`.
When a descriptor transitions to this state, we check it's neighbors, and merge them together accordingly, e.g.:

`(Reserved, Free, Reserved) -> (Reserved, Free, Free) -> (Reserved, Free)` (2nd and 3rd entries merged)

`(Free, Reserved, Free) -> (Free, Free, Free) -> (Free)` (all 3 entries merged into 1)

# Design
## Naive Approach
Prior to the above change, descriptors were stored in a LinkedList, which was obviously not great. It meant O(n)
lookups everywhere.
```
struct RangeAllocator<T> {
    list: LinkedList<Box<Descriptor<T>>>
}
```

## Using RBTree
We improved this with a combination of two RBTree fields:
```
struct RangeAllocator<T> {
    // all descriptors by offset
    tree: RBTree<usize, Descriptor<T>>
    // free descriptors by (size, offset)
    free_tree: RBTree((usize, usize), ())
}
```

RBTree allows storing user defined structs as keys, provided they are ordered.  A tuple of integers naturally satisfies this constraint.
By storing `(size, offset)`, we're able to provide `O(log(n))` lookup of a "best sized" free descriptor.  Since `XArray` only supports
integer keys, we see the following options:

# Migration Options

## Option 1: Use XArray<Box<LinkedList<usize>>>
```
struct RangeAllocator<T> {
    // all descriptors by offset
    descriptors: XArray<Box<Descriptor<T>>>,
    // free descriptors by size
    free_offsets: XArray<Box<LinkedList<usize>>>
}
```

TODO: Get help explaining why this is bad.  I guess We'd have 3 layers of pointers to an integer which is inefficient? I
I'm also not sure how awkward iterating/modifying a list behind those wrappers will be.

## Option 2: Add `prev_same_size` and `next_same_size` to `Descriptor<T>`
```
struct Descriptor<T> {
    // other fields
    prev_same_size_index: Option<usize>
    next_same_size_index: Option<usize>
}


struct RangeAllocator<T> {
    descriptors: XArray<Box<Descriptor<T>>>,
    free_indices: XArray<Box<usize>>
}
```
In this option, we store a single free index in the XArray, and are able to check other descriptors of the same size
via these two fields on the `Descriptor` itself.  The obvious downside here is introducing lots of complexity to keep
track of all descriptors of a given size, updating these links accordingly.

## Option 3: Use another data structure?
Is there some other data structure/aproach that we haven't thought of.  We're very open to suggestions :-)

Thanks in advance,

Matt


