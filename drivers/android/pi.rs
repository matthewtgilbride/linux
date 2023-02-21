// SPDX-License-Identifier: GPL-2.0

use kernel::task::Task;
use kernel::sync::SpinLock;
use kernel::pr_err;

use core::mem::MaybeUninit;
use core::marker::PhantomPinned;
use core::cell::UnsafeCell;
use core::pin::Pin;

// TODO: We need methods from the rtmutex API that are not exposed to drivers, and only defined in
// `kernel/locking/rtmutex_common.h`. For now, we just define them here instead of trying to get
// bindgen to generate the bindings.
mod bindings {
    #![allow(non_camel_case_types)]
    #![allow(improper_ctypes)]
    use kernel::bindings as kbind;

    use core::ffi::{c_uint, c_int, c_ulong, c_void};
    use core::ptr::addr_of_mut;

    #[repr(C)]
    pub(super) struct rt_mutex_base {
        wait_lock: kbind::raw_spinlock_t,
        waiters: kbind::rb_root_cached,
        owner: *mut kbind::task_struct,
    }

    #[repr(C)]
    pub(super) struct rt_mutex_waiter {
        tree_entry: kbind::rb_node,
        pi_tree_entry: kbind::rb_node,
        task: *mut kbind::task_struct,
        lock: *mut rt_mutex_base,
        wake_state: c_uint,
        prio: c_int,
        deadline: u64,
        ww_ctx: *mut c_void,
    }

    extern "C" {
        pub(super) fn rt_mutex_futex_unlock(lock: *mut rt_mutex_base);

        pub(super) fn rt_mutex_init_proxy_locked(lock: *mut rt_mutex_base, proxy_owner: *mut kbind::task_struct);
        pub(super) fn rt_mutex_proxy_unlock(lock: *mut rt_mutex_base) -> c_int;
        pub(super) fn rt_mutex_cleanup_proxy_lock(lock: *mut rt_mutex_base, waiter: *mut rt_mutex_waiter) -> bool;
        pub(super) fn rt_mutex_start_proxy_lock(
            lock: *mut rt_mutex_base,
            waiter: *mut rt_mutex_waiter,
            task: *mut kbind::task_struct
        ) -> c_int;
    }

    // This is a C macro, so we can't just put it in the `extern "C"` block.
    unsafe fn rb_clear_node(node: *mut kbind::rb_node) {
        // #define RB_CLEAR_NODE(node) ((node)->__rb_parent_color = (unsigned long)(node))
        unsafe {
            let __rb_parent_color = addr_of_mut!((*node).__rb_parent_color);
            core::ptr::write(__rb_parent_color, node as c_ulong);
        }
    }

    // This is an inline method, so we can't just put it in the `extern "C"` block.
    pub(super) unsafe fn rt_mutex_init_waiter(waiter: *mut rt_mutex_waiter) {
        unsafe {
            #[cfg(CONFIG_DEBUG_RT_MUTEXES)]
            core::ptr::write_bytes(waiter as *mut u8, 0x11, core::mem::size_of::<rt_mutex_waiter>());

            rb_clear_node(addr_of_mut!((*waiter).pi_tree_entry));
            rb_clear_node(addr_of_mut!((*waiter).tree_entry));
            core::ptr::write(addr_of_mut!((*waiter).wake_state), kbind::TASK_NORMAL);
            core::ptr::write(addr_of_mut!((*waiter).task), core::ptr::null_mut());
        }
    }

    // This is an inline method, so we can't just put it in the `extern "C"` block.
    #[cfg(CONFIG_DEBUG_RT_MUTEXES)]
    pub(super) unsafe fn rt_mutex_free_waiter(waiter: *mut rt_mutex_waiter) {
        unsafe {
            core::ptr::write_bytes(waiter as *mut u8, 0x22, core::mem::size_of::<rt_mutex_waiter>());
        }
    }

    // This is an inline method, so we can't just put it in the `extern "C"` block.
    #[cfg(not(CONFIG_DEBUG_RT_MUTEXES))]
    pub(super) unsafe fn rt_mutex_free_waiter(_: *mut rt_mutex_waiter) {
    }
}

pub(crate) struct PINode {
    /// Initialized when bit 1 is set.
    rt_mutex: UnsafeCell<MaybeUninit<bindings::rt_mutex_base>>,
    rt_waiter: UnsafeCell<MaybeUninit<bindings::rt_mutex_waiter>>,
    waiter: *mut kernel::bindings::task_struct,
    inner: SpinLock<PINodeInner>,
    _pinned: PhantomPinned,
}

struct PINodeInner {
    /// Written when assigning owner. Read-only once bit 1 is set.
    owner: *mut kernel::bindings::task_struct,
    /// Bits:
    /// 1 - Is assigned to an owning thread?
    /// 2 - Is the waiting thread waiting?
    /// 3 - Does the waiting thread have an active proxy lock operation?
    /// 4 - Owner has released the lock.
    state: u8,
}

const OWNER_SET: u8 = 1;
const WAITER_WAITING: u8 = 2;
const ACTIVE_PROXY_LOCK: u8 = 4;
const OWNER_IS_DONE: u8 = 8;

impl PINode {
    /// # Safety
    ///
    /// Must be initialized before use.
    pub(crate) unsafe fn new(waiter: &Task) -> Self {
        Self {
            rt_mutex: UnsafeCell::new(MaybeUninit::uninit()),
            rt_waiter: UnsafeCell::new(MaybeUninit::uninit()),
            waiter: waiter.as_raw(),
            // SAFETY: Caller promises to initialize us, and we call `spinlock_init` there.
            inner: unsafe {
                SpinLock::new(PINodeInner {
                    owner: core::ptr::null_mut(),
                    state: 0,
                })
            },
            _pinned: PhantomPinned,
        }
    }

    pub(crate) fn init(self: Pin<&mut Self>) {
        // SAFETY: This just performs a pin projection and calls a C FFI method.
        unsafe {
            let me = Pin::into_inner_unchecked(self);
            let inner = Pin::new_unchecked(&mut me.inner);
            kernel::spinlock_init!(inner, "PINode::init");

            bindings::rt_mutex_init_waiter(me.rt_waiter());
        }
    }

    fn rt_mutex(&self) -> *mut bindings::rt_mutex_base {
        self.rt_mutex.get() as *mut bindings::rt_mutex_base
    }

    fn rt_waiter(&self) -> *mut bindings::rt_mutex_waiter {
        self.rt_waiter.get() as *mut bindings::rt_mutex_waiter
    }

    pub(crate) fn set_owner(&self, owner: &kernel::task::Task) {
        let owner = owner.as_raw();
        if owner == self.waiter {
            return;
        }

        let mut inner = self.inner.lock();
        if inner.state & OWNER_SET != 0 {
            if owner != inner.owner {
                pr_err!("set_owner called twice with two different owners");
            }
            return;
        }
        inner.owner = owner;

        // SAFETY: This field is initialized together with OWNER_SET.
        unsafe {
            bindings::rt_mutex_init_proxy_locked(self.rt_mutex(), owner);
        }

        // Only possible states here are 0 and WAITER_WAITING
        if inner.state == WAITER_WAITING {
            // SAFETY: We know that the waiter will clean up the start_proxy_lock when it stops
            // sleeping.
            let res = unsafe {
                bindings::rt_mutex_start_proxy_lock(self.rt_mutex(), self.rt_waiter(), self.waiter)
            };

            // The call can only fail in two situations:
            //  1. Acquiring the mutex succeeds.
            //  2. A deadlock is detected.
            //
            // The first situation can't happen because we just initialized the mutex to be locked
            // by `owner`, so `waiter` cannot acquire it.
            //
            // The second situation can't happen because `owner != waiter`.
            if res != 0 {
                drop(inner);
                pr_err!("rt_mutex_start_proxy_lock failed when it shouldn't");
                unsafe {
                    kernel::bindings::BUG();
                }
                return;
            }
            inner.state = OWNER_SET | WAITER_WAITING | ACTIVE_PROXY_LOCK;
        } else {
            inner.state = OWNER_SET;
        }
    }

    /// Must be called from the owner.
    pub(crate) fn owner_is_done(&self) {
        let current = unsafe { kernel::bindings::get_current() };

        let mut inner = self.inner.lock();
        if inner.state & OWNER_SET == 0 {
            // This happens when `owner == waiter`.
            return;
        }
        if inner.state & OWNER_IS_DONE != 0 {
            return;
        }

        if inner.owner != current {
            pr_err!("owner_is_done called on wrong thread");
            return;
        }

        inner.state |= OWNER_IS_DONE;
        drop(inner);

        // SAFETY: We are on the owner task, the owner has been given the lock using
        // init_proxy_locked, and the owner has not yet released the lock.
        unsafe {
            bindings::rt_mutex_futex_unlock(self.rt_mutex());
        }
    }

    /// Must be called from the waiter.
    pub(crate) fn begin_sleep(&self) {
        let current = unsafe { kernel::bindings::get_current() };

        let mut inner = self.inner.lock();
        if self.waiter != current {
            pr_err!("begin_sleep called on wrong thread");
            return;
        }
        if inner.state & WAITER_WAITING != 0 {
            pr_err!("begin_sleep called while sleeping");
            return;
        }

        inner.state |= WAITER_WAITING;
        if inner.state & OWNER_SET == 0 {
            // Here we don't do anything. If the owner gets set during sleep, then the owner will
            // start the lock acquisition for us.
            return;
        }
        if inner.state & OWNER_IS_DONE != 0 {
            // We don't do anything in this case.
            return;
        }
        inner.state |= ACTIVE_PROXY_LOCK;
        drop(inner);

        // SAFETY: We are the waiter, and `set_owner` has already run, so it wont also attempt to
        // take the lock.
        let res = unsafe {
            bindings::rt_mutex_start_proxy_lock(self.rt_mutex(), self.rt_waiter(), self.waiter)
        };

        if res == 0 {
            // We are now ready to sleep.
        } else if res == 1 {
            // `owner_is_done` has been called. We release the lock again because we don't need it.
            //
            // SAFETY: Once `owner_is_done` has been called, only the waiter (us) will access the
            // rtmutex.
            unsafe {
                bindings::rt_mutex_proxy_unlock(self.rt_mutex());
            }

            // Signal to the `end_sleep` call that we don't have an active proxy lock op.
            inner = self.inner.lock();
            inner.state &= !ACTIVE_PROXY_LOCK;
            drop(inner);
        } else {
            inner = self.inner.lock();
            inner.state &= !ACTIVE_PROXY_LOCK;
            drop(inner);

            pr_err!("rt_mutex_start_proxy_lock detected a deadlock");
        }
    }

    pub(crate) fn end_sleep(&self) {
        let current = unsafe { kernel::bindings::get_current() };

        let mut inner = self.inner.lock();
        if self.waiter != current {
            pr_err!("begin_sleep called on wrong thread");
            return;
        }
        if inner.state & WAITER_WAITING == 0 {
            pr_err!("end_sleep called without begin_sleep");
            return;
        }

        let should_stop_lock = inner.state & ACTIVE_PROXY_LOCK != 0;
        inner.state &= !(WAITER_WAITING | ACTIVE_PROXY_LOCK);
        drop(inner);

        if should_stop_lock {
            let cleanup_succ = unsafe {
                bindings::rt_mutex_cleanup_proxy_lock(self.rt_mutex(), self.rt_waiter())
            };

            if !cleanup_succ {
                // `owner_is_done` has been called, giving us the rtmutex.
                //
                // SAFETY: Once `owner_is_done` has been called, only the waiter (us) will access the
                // rtmutex.
                unsafe {
                    bindings::rt_mutex_proxy_unlock(self.rt_mutex());
                }
            }
        }
    }
}

impl Drop for PINode {
    fn drop(&mut self) {
        let inner = self.inner.lock();

        if inner.state & WAITER_WAITING != 0 {
            pr_err!("PINode dropped during waiter sleep.");
        }

        let owner_set = inner.state & OWNER_SET != 0;
        let owner_is_done = inner.state & OWNER_IS_DONE != 0;
        if owner_set && !owner_is_done {
            // SAFETY: We are the only ones who can access the rtmutex, so its ok to unlock it in
            // an unsynchronized manner.
            unsafe {
                bindings::rt_mutex_proxy_unlock(self.rt_mutex());
            }
        }

        // SAFETY: This just cleans up the waiter.
        unsafe {
            bindings::rt_mutex_free_waiter(self.rt_waiter());
        }
    }
}
