// SPDX-License-Identifier: GPL-2.0

use kernel::{
    linked_list::{GetLinks, Links, List},
    prelude::*,
    security,
    str::{CStr, CString},
    sync::{Arc, Mutex},
    task::Kuid,
};

use crate::{error::BinderError, node::NodeRef, process::Process};

// This module defines the global variable containing the list of contexts. Since the
// `kernel::sync` bindings currently don't support mutexes in globals, we use a temporary
// workaround.
//
// TODO: Once `kernel::sync` has support for mutexes in globals, remove this module.
mod context_global {
    use super::ContextList;
    use core::cell::UnsafeCell;
    use core::mem::MaybeUninit;
    use kernel::init::PinInit;
    use kernel::linked_list::List;
    use kernel::sync::lock::mutex::{Mutex, MutexBackend};
    use kernel::sync::lock::Guard;

    /// A temporary wrapper used to define a mutex in a global.
    pub(crate) struct Contexts {
        inner: UnsafeCell<MaybeUninit<Mutex<ContextList>>>,
    }

    impl Contexts {
        /// Called when the module is initialized.
        pub(crate) fn init(&self) {
            // SAFETY: This is only called during initialization of the binder module, so we know
            // that the global is currently uninitialized and that nobody else is using it yet.
            unsafe {
                let ptr = self.inner.get() as *mut Mutex<ContextList>;
                let init = kernel::new_mutex!(ContextList { list: List::new() }, "ContextList");
                match init.__pinned_init(ptr) {
                    Ok(()) => {}
                    Err(e) => match e {},
                }
            }
        }

        pub(crate) fn lock(&self) -> Guard<'_, ContextList, MutexBackend> {
            // SAFETY: The `init` method is called during initialization of the binder module, so the
            // mutex is always initialized when this method is called.
            unsafe {
                let ptr = self.inner.get() as *const Mutex<ContextList>;
                (*ptr).lock()
            }
        }
    }

    unsafe impl Send for Contexts {}
    unsafe impl Sync for Contexts {}

    pub(crate) static CONTEXTS: Contexts = Contexts {
        inner: UnsafeCell::new(MaybeUninit::uninit()),
    };
}

pub(crate) use self::context_global::CONTEXTS;

pub(crate) struct ContextList {
    list: List<Arc<Context>>,
}

pub(crate) fn get_all_contexts() -> Result<Vec<Arc<Context>>> {
    let mut lock = CONTEXTS.lock();

    let count = {
        let mut count = 0;
        let mut cursor = lock.list.cursor_front();
        while cursor.current().is_some() {
            count += 1;
            cursor.move_next();
        }
        count
    };

    // TODO: The current cursor API gives me a `&Context` rather than a `&Arc<Context>`, so I
    // can't call clone to get a `Arc<Context>` via a cursor.
    let mut ctxs = Vec::try_with_capacity(count)?;
    while let Some(cur) = lock.list.pop_front() {
        ctxs.try_push(cur)?;
    }
    for ctx in &ctxs {
        lock.list.push_back(ctx.clone());
    }
    Ok(ctxs)
}

/// This struct keeps track of the processes using this context, and which process is the context
/// manager.
struct Manager {
    node: Option<NodeRef>,
    uid: Option<Kuid>,
    all_procs: List<Arc<Process>>,
}

/// There is one context per binder file (/dev/binder, /dev/hwbinder, etc)
#[pin_data]
pub(crate) struct Context {
    #[pin]
    manager: Mutex<Manager>,
    pub(crate) name: CString,
    links: Links<Context>,
}

impl GetLinks for Context {
    type EntryType = Context;
    fn get_links(data: &Context) -> &Links<Context> {
        &data.links
    }
}

impl Context {
    pub(crate) fn new(name: &CStr) -> Result<Arc<Self>> {
        let name = CString::try_from(name)?;
        let ctx = Arc::pin_init(pin_init!(Context {
            name,
            links: Links::new(),
            manager <- kernel::new_mutex!(Manager {
                all_procs: List::new(),
                node: None,
                uid: None,
            }, "Context::manager"),
        }))?;

        CONTEXTS.lock().list.push_back(ctx.clone());

        Ok(ctx)
    }

    /// Called when the file for this context is unlinked.
    ///
    /// No-op if called twice.
    pub(crate) fn deregister(self: &Arc<Self>) {
        // SAFETY: We never add the context to any other linked list than this one, so it is either
        // in this list, or not in any list.
        unsafe {
            CONTEXTS.lock().list.remove(self);
        }
    }

    pub(crate) fn register_process(self: &Arc<Self>, proc: Arc<Process>) {
        if !Arc::ptr_eq(self, &proc.ctx) {
            pr_err!("Context::register_process called on the wrong context.");
            return;
        }
        self.manager.lock().all_procs.push_back(proc);
    }

    pub(crate) fn deregister_process(self: &Arc<Self>, proc: &Arc<Process>) {
        if !Arc::ptr_eq(self, &proc.ctx) {
            pr_err!("Context::deregister_process called on the wrong context.");
            return;
        }
        // SAFETY: We just checked that this is the right list.
        unsafe {
            self.manager.lock().all_procs.remove(proc);
        }
    }

    pub(crate) fn set_manager_node(&self, node_ref: NodeRef) -> Result {
        let mut manager = self.manager.lock();
        if manager.node.is_some() {
            pr_warn!("BINDER_SET_CONTEXT_MGR already set");
            return Err(EBUSY);
        }
        security::binder_set_context_mgr(&node_ref.node.owner.cred)?;

        // If the context manager has been set before, ensure that we use the same euid.
        let caller_uid = Kuid::current_euid();
        if let Some(ref uid) = manager.uid {
            if *uid != caller_uid {
                return Err(EPERM);
            }
        }

        manager.node = Some(node_ref);
        manager.uid = Some(caller_uid);
        Ok(())
    }

    pub(crate) fn unset_manager_node(&self) {
        let node_ref = self.manager.lock().node.take();
        drop(node_ref);
    }

    pub(crate) fn get_manager_node(&self, strong: bool) -> Result<NodeRef, BinderError> {
        self.manager
            .lock()
            .node
            .as_ref()
            .ok_or_else(BinderError::new_dead)?
            .clone(strong)
            .map_err(BinderError::from)
    }

    pub(crate) fn for_each_proc<F>(&self, mut func: F)
    where
        F: FnMut(&Process),
    {
        let lock = self.manager.lock();
        let mut cursor = lock.all_procs.cursor_front();
        while let Some(proc) = cursor.current() {
            func(proc);
            cursor.move_next();
        }
    }

    pub(crate) fn get_all_procs(&self) -> Result<Vec<Arc<Process>>> {
        let mut lock = self.manager.lock();

        let count = {
            let mut count = 0;
            let mut cursor = lock.all_procs.cursor_front();
            while cursor.current().is_some() {
                count += 1;
                cursor.move_next();
            }
            count
        };

        // TODO: The current cursor API gives me a `&Process` rather than a `&Arc<Process>`, so I
        // can't call clone to get a `Arc<Process>` via a cursor.
        //
        // When the linked list is fixed, we can simplify this a lot.
        let mut procs = Vec::try_with_capacity(count)?;
        while let Some(cur) = lock.all_procs.pop_front() {
            // This won't fail because we allocated enough capacity to hold all of them.
            procs.try_push(cur)?;
        }
        for proc in &procs {
            lock.all_procs.push_back(proc.clone());
        }
        Ok(procs)
    }

    pub(crate) fn get_procs_with_pid(&self, pid: i32) -> Result<Vec<Arc<Process>>> {
        let mut procs = self.get_all_procs()?;
        procs.retain(|proc| proc.task.pid() == pid);
        Ok(procs)
    }
}
