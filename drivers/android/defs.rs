// SPDX-License-Identifier: GPL-2.0

use core::ops::{Deref, DerefMut};
use kernel::{
    bindings,
    io_buffer::{ReadableFromBytes, WritableToBytes},
};

macro_rules! decl_wrapper {
    ($newname:ident, $wrapped:ty) => {
        #[derive(Copy, Clone, Default)]
        #[repr(transparent)]
        pub(crate) struct $newname($wrapped);
        // SAFETY: This macro is only used with types where this is ok.
        unsafe impl ReadableFromBytes for $newname {}
        unsafe impl WritableToBytes for $newname {}
        impl Deref for $newname {
            type Target = $wrapped;
            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }
        impl DerefMut for $newname {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.0
            }
        }
    };
}

decl_wrapper!(BinderVersion, bindings::binder_version);

impl BinderVersion {
    pub(crate) fn current() -> Self {
        Self(bindings::binder_version {
            protocol_version: bindings::BINDER_CURRENT_PROTOCOL_VERSION as _,
        })
    }
}
