// SPDX-License-Identifier: GPL-2.0

//! Binder -- the Android IPC mechanism.
//!
//! TODO: This module is a work in progress.

use kernel::{
    io_buffer::IoBufferWriter,
    linked_list::{GetLinks, GetLinksWrapped, Links},
    file::{File, PollTable, Operations},
    prelude::*,
    str::CStr,
    sync::Ref,
    user_ptr::UserSlicePtrWriter,
    PointerWrapper,
    bindings,
};

#[cfg(not(CONFIG_ANDROID_BINDERFS_RUST))]
use kernel::miscdev::Registration;

use core::mem::ManuallyDrop;

#[macro_use]
mod debug;

mod allocation;
mod context;
mod defs;
mod node;
mod process;
mod range_alloc;
mod thread;
mod transaction;

use {context::Context, thread::Thread, process::Process};

module! {
    type: BinderModule,
    name: b"rust_binder",
    author: b"Wedson Almeida Filho",
    description: b"Android Binder",
    license: b"GPL",
}

trait DeliverToRead {
    /// Performs work. Returns true if remaining work items in the queue should be processed
    /// immediately, or false if it should return to caller before processing additional work
    /// items.
    fn do_work(self: Ref<Self>, thread: &Thread, writer: &mut UserSlicePtrWriter) -> Result<bool>;

    /// Cancels the given work item. This is called instead of [`DeliverToRead::do_work`] when work
    /// won't be delivered.
    fn cancel(self: Ref<Self>) {}

    /// Returns the linked list links for the work item.
    fn get_links(&self) -> &Links<dyn DeliverToRead>;

    /// Should we use `wake_up_interruptible_sync` or `wake_up_interruptible` when scheduling this
    /// work item?
    ///
    /// Generally only set to true for non-oneway transactions.
    fn should_sync_wakeup(&self) -> bool;

    /// Get the debug name of this type.
    fn debug_name(&self) -> &'static str {
        core::any::type_name::<Self>()
    }
}

struct DeliverToReadListAdapter {}

impl GetLinks for DeliverToReadListAdapter {
    type EntryType = dyn DeliverToRead;

    fn get_links(data: &Self::EntryType) -> &Links<Self::EntryType> {
        data.get_links()
    }
}

impl GetLinksWrapped for DeliverToReadListAdapter {
    type Wrapped = Ref<dyn DeliverToRead>;
}

struct DeliverCode {
    code: u32,
    links: Links<dyn DeliverToRead>,
}

impl DeliverCode {
    fn new(code: u32) -> Self {
        Self {
            code,
            links: Links::new(),
        }
    }
}

impl DeliverToRead for DeliverCode {
    fn do_work(self: Ref<Self>, _thread: &Thread, writer: &mut UserSlicePtrWriter) -> Result<bool> {
        writer.write(&self.code)?;
        Ok(true)
    }

    fn get_links(&self) -> &Links<dyn DeliverToRead> {
        &self.links
    }

    fn should_sync_wakeup(&self) -> bool {
        false
    }
}

const fn ptr_align(value: usize) -> usize {
    let size = core::mem::size_of::<usize>() - 1;
    (value + size) & !size
}

unsafe impl Sync for BinderModule {}

struct BinderModule {
    #[cfg(not(CONFIG_ANDROID_BINDERFS_RUST))]
    _reg: Pin<Box<Registration<Process>>>,
}

#[cfg(not(CONFIG_ANDROID_BINDERFS_RUST))]
impl kernel::Module for BinderModule {
    fn init(name: &'static CStr, _module: &'static kernel::ThisModule) -> Result<Self> {
        let ctx = Context::new(name)?;
        let reg = Registration::new_pinned(fmt!("{name}"), ctx)?;

        Ok(Self {
            _reg: reg,
        })
    }
}

#[cfg(CONFIG_ANDROID_BINDERFS_RUST)]
impl kernel::Module for BinderModule {
    fn init(_name: &'static CStr, _module: &'static kernel::ThisModule) -> Result<Self> {
        unsafe {
            kernel::error::to_result(bindings::init_rust_binderfs())?;
        }

        Ok(Self { })
    }
}

/// Makes the inner type Sync.
#[repr(transparent)]
pub struct AssertSync<T>(T);
unsafe impl<T> Sync for AssertSync<T> {}

/// File operations that rust_binderfs.c can use.
#[no_mangle]
#[used]
pub static rust_binder_fops: AssertSync<kernel::bindings::file_operations> = {
    let ops = kernel::bindings::file_operations {
        owner: THIS_MODULE.as_ptr(),
        poll: Some(rust_binder_poll),
        unlocked_ioctl: Some(rust_binder_unlocked_ioctl),
        compat_ioctl: Some(rust_binder_compat_ioctl),
        mmap: Some(rust_binder_mmap),
        open: Some(rust_binder_open),
        release: Some(rust_binder_release),
        llseek: None,
        read: None,
        write: None,
        read_iter: None,
        write_iter: None,
        iopoll: None,
        iterate: None,
        iterate_shared: None,
        mmap_supported_flags: 0,
        flush: Some(rust_binder_flush),
        fsync: None,
        fasync: None,
        lock: None,
        sendpage: None,
        get_unmapped_area: None,
        check_flags: None,
        flock: None,
        splice_write: None,
        splice_read: None,
        setlease: None,
        fallocate: None,
        show_fdinfo: None,
        copy_file_range: None,
        remap_file_range: None,
        fadvise: None,
        uring_cmd: None,
    };

    AssertSync(ops)
};

#[no_mangle]
unsafe extern "C" fn rust_binder_new_device(name: *const core::ffi::c_char) -> *mut core::ffi::c_void {
    let name = unsafe { kernel::str::CStr::from_char_ptr(name) };

    match Context::new(name) {
        Ok(ctx) => Ref::into_raw(ctx) as *mut core::ffi::c_void,
        Err(_err) => return core::ptr::null_mut(),
    }
}

#[no_mangle]
unsafe extern "C" fn rust_binder_remove_device(device: *mut core::ffi::c_void) {
    if !device.is_null() {
        // SAFETY: The caller ensures that the pointer is valid.
        unsafe {
            let ctx: Ref<Context> = Ref::from_raw(device.cast());
            ctx.deregister();
            drop(ctx);
        }
    }
}

unsafe extern "C" fn rust_binder_open(inode: *mut bindings::inode, file: *mut bindings::file) -> core::ffi::c_int {
    // SAFETY: The `rust_binderfs.c` file ensures that `i_private` is set to the return value of a
    // successful call to `rust_binder_new_device`. Here we use `ManuallyDrop` to avoid dropping
    // the ref-count when `ctx` goes out of scope, as we are only borrowing the context here.
    let ctx: ManuallyDrop<Ref<Context>> = unsafe {
        ManuallyDrop::new(Ref::from_raw((*inode).i_private.cast()))
    };

    let process = match Process::open(&*ctx, unsafe { File::from_ptr(file) }) {
        Ok(process) => process,
        Err(err) => return err.to_kernel_errno(),
    };

    unsafe { (*file).private_data = process.into_pointer() as *mut core::ffi::c_void; }

    0
}

unsafe extern "C" fn rust_binder_release(_inode: *mut bindings::inode, file: *mut bindings::file) -> core::ffi::c_int {
    let process: Ref<Process> = unsafe { Ref::from_pointer((*file).private_data) };
    let file = unsafe { File::from_ptr(file) };
    Process::release(process, file);
    0
}

unsafe extern "C" fn rust_binder_compat_ioctl(
    file: *mut bindings::file,
    cmd: core::ffi::c_uint,
    arg: core::ffi::c_ulong,
) -> core::ffi::c_long {
    let f = unsafe { Ref::borrow((*file).private_data) };
    let mut cmd = kernel::file::IoctlCommand::new(cmd as _, arg as _);
    match Process::compat_ioctl(f, unsafe { File::from_ptr(file) }, &mut cmd) {
        Ok(ret) => ret.into(),
        Err(err) => err.to_kernel_errno().into(),
    }
}

unsafe extern "C" fn rust_binder_unlocked_ioctl(
    file: *mut bindings::file,
    cmd: core::ffi::c_uint,
    arg: core::ffi::c_ulong,
) -> core::ffi::c_long {
    let f = unsafe { Ref::borrow((*file).private_data) };
    let mut cmd = kernel::file::IoctlCommand::new(cmd as _, arg as _);
    match Process::ioctl(f, unsafe { File::from_ptr(file) }, &mut cmd) {
        Ok(ret) => ret.into(),
        Err(err) => err.to_kernel_errno().into(),
    }
}

unsafe extern "C" fn rust_binder_mmap(
    file: *mut bindings::file,
    vma: *mut bindings::vm_area_struct,
) -> core::ffi::c_int {
    let f = unsafe { Ref::borrow((*file).private_data) };
    let mut area = unsafe { kernel::mm::virt::Area::from_ptr(vma) };
    match Process::mmap(f, unsafe { File::from_ptr(file) }, &mut area) {
        Ok(()) => 0,
        Err(err) => err.to_kernel_errno().into(),
    }
}

unsafe extern "C" fn rust_binder_poll(
    file: *mut bindings::file,
    wait: *mut bindings::poll_table_struct,
) -> bindings::__poll_t {
    let f = unsafe { Ref::borrow((*file).private_data) };
    let fileref = unsafe { File::from_ptr(file) };
    match Process::poll(f, fileref, unsafe {
        &PollTable::from_ptr(wait)
    }) {
        Ok(v) => v,
        Err(_) => bindings::POLLERR,
    }
}

unsafe extern "C" fn rust_binder_flush(
    file: *mut bindings::file,
    _id: bindings::fl_owner_t,
) -> core::ffi::c_int {
    let f = unsafe { Ref::borrow((*file).private_data) };
    match Process::flush(f) {
        Ok(()) => 0,
        Err(err) => err.to_kernel_errno().into(),
    }
}
