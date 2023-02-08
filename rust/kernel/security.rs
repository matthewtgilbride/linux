// SPDX-License-Identifier: GPL-2.0

//! Linux Security Modules (LSM).
//!
//! C header: [`include/linux/security.h`](../../../../include/linux/security.h).

use crate::{bindings, cred::Credential, file::File, to_result, Result};

/// Calls the security modules to determine if the given task can become the manager of a binder
/// context.
pub fn binder_set_context_mgr(mgr: &Credential) -> Result {
    // SAFETY: `mrg.0` is valid because the shared reference guarantees a nonzero refcount.
    to_result(unsafe { bindings::security_binder_set_context_mgr(mgr.0.get()) })
}

/// Calls the security modules to determine if binder transactions are allowed from task `from` to
/// task `to`.
pub fn binder_transaction(from: &Credential, to: &Credential) -> Result {
    // SAFETY: `from` and `to` are valid because the shared references guarantee nonzero refcounts.
    to_result(unsafe { bindings::security_binder_transaction(from.0.get(), to.0.get()) })
}

/// Calls the security modules to determine if task `from` is allowed to send binder objects
/// (owned by itself or other processes) to task `to` through a binder transaction.
pub fn binder_transfer_binder(from: &Credential, to: &Credential) -> Result {
    // SAFETY: `from` and `to` are valid because the shared references guarantee nonzero refcounts.
    to_result(unsafe { bindings::security_binder_transfer_binder(from.0.get(), to.0.get()) })
}

/// Calls the security modules to determine if task `from` is allowed to send the given file to
/// task `to` (which would get its own file descriptor) through a binder transaction.
pub fn binder_transfer_file(from: &Credential, to: &Credential, file: &File) -> Result {
    // SAFETY: `from`, `to` and `file` are valid because the shared references guarantee nonzero
    // refcounts.
    to_result(unsafe {
        bindings::security_binder_transfer_file(from.0.get(), to.0.get(), file.0.get())
    })
}

/// This struct contains a security context string.
///
/// The struct has the invariant that it always contains a valid security context.
pub struct SecurityCtx {
    secdata: *mut core::ffi::c_char,
    seclen: usize,
}

impl SecurityCtx {
    /// Get the security context given its id.
    pub fn from_secid(secid: u32) -> Result<Self> {
        let mut secdata = core::ptr::null_mut();
        let mut seclen = 0;
        // SAFETY: Just a C FFI call. The pointers are valid for writes.
        unsafe {
            to_result(bindings::security_secid_to_secctx(secid, &mut secdata, &mut seclen))?;
        }
        // If the above call did not fail, then we have a valid security
        // context, so the invariants are not violated.
        Ok(Self {
            secdata,
            seclen: seclen as usize,
        })
    }

    /// Returns the length of this security context.
    pub fn len(&self) -> usize {
        self.seclen
    }

    /// Returns the bytes for this security context.
    pub fn as_bytes(&self) -> &[u8] {
        // SAFETY: This is safe by the invariant of this type.
        unsafe {
            core::slice::from_raw_parts(self.secdata.cast(), self.seclen)
        }
    }
}

impl Drop for SecurityCtx {
    fn drop(&mut self) {
        // SAFETY: The invariants of this type guarantee that the security
        // context is valid.
        unsafe {
            bindings::security_release_secctx(self.secdata, self.seclen as u32);
        }
    }
}
