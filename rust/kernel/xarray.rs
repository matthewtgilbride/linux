// SPDX-License-Identifier: GPL-2.0

//! XArray abstraction.
//!
//! C header: [`include/linux/xarray.h`](../../include/linux/xarray.h)

use crate::{
    bindings,
    error::{Error, Result},
    types::{ForeignOwnable, Opaque, ScopeGuard},
};
use core::{
    marker::{PhantomData, PhantomPinned},
    pin::Pin,
    ptr::NonNull,
};

/// Flags passed to `XArray::new` to configure the `XArray`.
type Flags = bindings::gfp_t;

/// Flag values passed to `XArray::new` to configure the `XArray`.
pub mod flags {
    /// Use IRQ-safe locking.
    pub const LOCK_IRQ: super::Flags = bindings::BINDINGS_XA_FLAGS_LOCK_IRQ;
    /// Use softirq-safe locking.
    pub const LOCK_BH: super::Flags = bindings::BINDINGS_XA_FLAGS_LOCK_BH;
    /// Track which entries are free (distinct from None).
    pub const TRACK_FREE: super::Flags = bindings::BINDINGS_XA_FLAGS_TRACK_FREE;
    /// Initialize array index 0 as busy.
    pub const ZERO_BUSY: super::Flags = bindings::BINDINGS_XA_FLAGS_ZERO_BUSY;
    /// Use GFP_ACCOUNT for internal memory allocations.
    pub const ACCOUNT: super::Flags = bindings::BINDINGS_XA_FLAGS_ACCOUNT;
    /// Create an allocating `XArray` starting at index 0.
    pub const ALLOC: super::Flags = bindings::BINDINGS_XA_FLAGS_ALLOC;
    /// Create an allocating `XArray` starting at index 1.
    pub const ALLOC1: super::Flags = bindings::BINDINGS_XA_FLAGS_ALLOC1;
}

/// Wrapper for a value owned by the `XArray` which holds the `XArray` lock until dropped.
pub struct ValueGuard<'a, T: ForeignOwnable>(NonNull<T>, Pin<&'a XArray<T>>);

impl<'a, T: ForeignOwnable> ValueGuard<'a, T> {
    /// Borrow the underlying value wrapped by the `ValueGuard`.
    ///
    /// Returns a `T::Borrowed` type for the owned `ForeignOwnable` type.
    pub fn borrow(&self) -> T::Borrowed<'_> {
        // SAFETY: The value is owned by the `XArray`, the lifetime it is borrowed for must not
        // outlive the `XArray` itself, nor the `ValueGuard` that holds the lock ensuring the value
        // remains in the `XArray`.
        unsafe { T::borrow(self.0.as_ptr() as _) }
    }
}

impl<'a, T: ForeignOwnable> Drop for ValueGuard<'a, T> {
    fn drop(&mut self) {
        // SAFETY: The XArray we have a reference to owns the C xarray object.
        unsafe { bindings::xa_unlock(self.1.xa.get()) };
    }
}

/// An array which efficiently maps sparse integer indices to owned objects.
///
/// This is similar to a `Vec<Option<T>>`, but more efficient when there are holes in the
/// index space, and can be efficiently grown.
///
/// This structure is expected to often be used with an inner type that can be efficiently
/// cloned, such as an `Arc<T>`.
///
pub struct XArray<T: ForeignOwnable> {
    xa: Opaque<bindings::xarray>,
    _p: PhantomData<T>,
    _q: PhantomPinned,
}

impl<T: ForeignOwnable> XArray<T> {
    /// Creates a new `XArray` with the given flags.
    pub fn new(flags: Flags) -> XArray<T> {
        let xa = Opaque::uninit();

        // SAFETY: We have just created `xa`. This data structure does not require
        // pinning.
        unsafe { bindings::xa_init_flags(xa.get(), flags) };

        // INVARIANT: Initialize the `XArray` with a valid `xa`.
        XArray {
            xa,
            _p: PhantomData,
            _q: PhantomPinned,
        }
    }

    /// Replaces an entry with a new value, returning the old value (if any).
    pub fn replace(self: Pin<&Self>, index: usize, value: T) -> Result<Option<T>> {
        let new = value.into_foreign();
        // SAFETY: `new` just came from into_foreign(), and we dismiss this guard if
        // the xa_store operation succeeds and takes ownership of the pointer.
        let guard = ScopeGuard::new(|| unsafe {
            T::from_foreign(new);
        });

        // SAFETY: `self.xa` is always valid by the type invariant, and we are storing
        // a `T::into_foreign()` result which upholds the later invariants.
        let old = unsafe {
            bindings::xa_store(
                self.xa.get(),
                index.try_into()?,
                new as *mut _,
                bindings::GFP_KERNEL,
            )
        };

        let ret = unsafe { bindings::xa_err(old) };
        if ret != 0 {
            Err(Error::from_errno(ret))
        } else if old.is_null() {
            guard.dismiss();
            Ok(None)
        } else {
            guard.dismiss();
            // SAFETY: The old value must have been stored by either this function or
            // `alloc_limits_opt`, both of which ensure non-NULL entries are valid
            // ForeignOwnable pointers.
            Ok(Some(unsafe { T::from_foreign(old) }))
        }
    }

    /// Replaces an entry with a new value, dropping the old value (if any).
    pub fn set(self: Pin<&Self>, index: usize, value: T) -> Result {
        self.replace(index, value)?;
        Ok(())
    }

    /// Looks up and returns a reference to an entry in the array, returning a `ValueGuard` if it
    /// exists.
    ///
    /// This guard blocks all other actions on the `XArray`. Callers are expected to drop the
    /// `ValueGuard` eagerly to avoid blocking other users, such as by taking a clone of the value.
    pub fn get(self: Pin<&Self>, index: usize) -> Option<ValueGuard<'_, T>> {
        // SAFETY: `self.xa` is always valid by the type invariant.
        unsafe { bindings::xa_lock(self.xa.get()) };

        // SAFETY: `self.xa` is always valid by the type invariant.
        let guard = ScopeGuard::new(|| unsafe { bindings::xa_unlock(self.xa.get()) });

        // SAFETY: `self.xa` is always valid by the type invariant.
        let p = unsafe { bindings::xa_load(self.xa.get(), index.try_into().ok()?) };

        NonNull::new(p as *mut T).map(|p| {
            guard.dismiss();
            ValueGuard(p, self)
        })
    }

    /// Looks up and returns a reference to an entry in the array, returning `(index, ValueGuard)`
    /// if it exists. If the index doesn't exist, returns the next larger index/value pair,
    /// else `None`.
    ///
    /// This guard blocks all other actions on the `XArray`. Callers are expected to drop the
    /// `ValueGuard` eagerly to avoid blocking other users, such as by taking a clone of the value.
    pub fn find(self: Pin<&Self>, index: usize) -> Option<(usize, ValueGuard<'_, T>)> {
        // SAFETY: `self.xa` is always valid by the type invariant.
        unsafe { bindings::xa_lock(self.xa.get()) };

        // SAFETY: `self.xa` is always valid by the type invariant.
        let guard = ScopeGuard::new(|| unsafe { bindings::xa_unlock(self.xa.get()) });

        let indexp = &mut index.try_into().ok()?;
        // SAFETY: `self.xa` is always valud by the type invariant.
        unsafe {
            bindings::xa_find(
                self.xa.get(),
                indexp,
                core::ffi::c_ulong::MAX,
                bindings::BINDINGS_XA_PRESENT,
            )
        };

        let new_index = *indexp;

        // SAFETY: `self.xa` is always valid by the type invariant.
        let p = unsafe { bindings::xa_load(self.xa.get(), new_index) };

        let new_index: usize = new_index.try_into().ok()?;

        NonNull::new(p as *mut T).map(|p| {
            guard.dismiss();
            (new_index, ValueGuard(p, self))
        })
    }

    /// Removes and returns an entry, returning it if it existed.
    pub fn remove(self: Pin<&Self>, index: usize) -> Option<T> {
        let p = unsafe { bindings::xa_erase(self.xa.get(), index.try_into().ok()?) };
        if p.is_null() {
            None
        } else {
            Some(unsafe { T::from_foreign(p) })
        }
    }
}

impl<T: ForeignOwnable> Drop for XArray<T> {
    fn drop(&mut self) {
        // SAFETY: `self.xa` is valid by the type invariant, and as we have the only reference to
        // the `XArray` we can safely iterate its contents and drop everything.
        unsafe {
            let mut index: core::ffi::c_ulong = 0;
            let mut entry = bindings::xa_find(
                self.xa.get(),
                &mut index,
                core::ffi::c_ulong::MAX,
                bindings::BINDINGS_XA_PRESENT,
            );
            while !entry.is_null() {
                T::from_foreign(entry);
                entry = bindings::xa_find_after(
                    self.xa.get(),
                    &mut index,
                    core::ffi::c_ulong::MAX,
                    bindings::BINDINGS_XA_PRESENT,
                );
            }

            // Locked locks are not safe to drop. Normally we would want to try_lock()/unlock() here
            // for safety or something similar, but in this case xa_destroy() is guaranteed to
            // acquire the lock anyway. This will deadlock if a lock guard was improperly dropped,
            // but that is not UB, so it's sufficient for soundness purposes.
            bindings::xa_destroy(self.xa.get());
        }
    }
}

// SAFETY: XArray is thread-safe and all mutation operations are internally locked.
unsafe impl<T: Send + ForeignOwnable> Send for XArray<T> {}
unsafe impl<T: Sync + ForeignOwnable> Sync for XArray<T> {}
