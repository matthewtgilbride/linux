// SPDX-License-Identifier: GPL-2.0

use kernel::{
    bindings,
    prelude::*,
    security,
    linked_list::{List, GetLinks, Links},
    sync::{Mutex, Ref, UniqueRef},
    str::{CStr, CString},
};

use crate::{
    node::NodeRef,
    process::Process,
    thread::{BinderError, BinderResult},
};

kernel::init_static_sync! {
    static CONTEXTS: Mutex<ContextList> = ContextList { list: List::new() };
}

struct ContextList {
    list: List<Ref<Context>>,
}

#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl Send for ContextList {}
unsafe impl Sync for ContextList {}

pub(crate) fn get_all_contexts() -> Result<Vec<Ref<Context>>> {
    let mut lock = CONTEXTS.lock();

    // TODO: The current cursor API gives me a `&Context` rather than a `&Ref<Context>`, so I
    // can't call clone to get a `Ref<Context>` via a cursor.
    let mut ctxs = Vec::new();
    while let Some(cur) = lock.list.pop_front() {
        ctxs.try_push(cur)?;
    }
    for ctx in &ctxs {
        lock.list.push_back(ctx.clone());
    }
    Ok(ctxs)
}

struct Manager {
    node: Option<NodeRef>,
    uid: Option<bindings::kuid_t>,
    all_procs: List<Ref<Process>>,
}

/// There is one context per binder file (/dev/binder, /dev/hwbinder, etc)
pub(crate) struct Context {
    manager: Mutex<Manager>,
    pub(crate) name: CString,
    links: Links<Context>,
}

#[allow(clippy::non_send_fields_in_send_ty)]
unsafe impl Send for Context {}
unsafe impl Sync for Context {}

impl GetLinks for Context {
    type EntryType = Context;
    fn get_links(data: &Context) -> &Links<Context> {
        &data.links
    }
}

impl Context {
    pub(crate) fn new(name: &CStr) -> Result<Ref<Self>> {
        let mut ctx = Pin::from(UniqueRef::try_new(Self {
            // SAFETY: Init is called below.
            manager: unsafe {
                Mutex::new(Manager {
                    node: None,
                    uid: None,
                    all_procs: List::new(),
                })
            },
            name: CString::try_from_cstr(name)?,
            links: Links::new(),
        })?);

        // SAFETY: `manager` is also pinned when `ctx` is.
        let manager = unsafe { ctx.as_mut().map_unchecked_mut(|c| &mut c.manager) };
        kernel::mutex_init!(manager, "Context::manager");

        let ctx: Ref<Self> = ctx.into();
        CONTEXTS.lock().list.push_back(ctx.clone());

        Ok(ctx)
    }

    /// Called when the file for this context is unlinked.
    ///
    /// No-op if called twice.
    pub(crate) fn deregister(self: &Ref<Self>) {
        // SAFETY: We never add the context to any other linked list than this one, so it is either
        // in this list, or not in any list.
        unsafe {
            CONTEXTS.lock().list.remove(self);
        }
    }

    pub(crate) fn register_process(self: &Ref<Self>, proc: Ref<Process>) {
        if !Ref::ptr_eq(self, &proc.ctx) {
            pr_err!("Context::register_process called on the wrong context.");
            return;
        }
        self.manager.lock().all_procs.push_back(proc);
    }

    pub(crate) fn deregister_process(self: &Ref<Self>, proc: &Ref<Process>) {
        if !Ref::ptr_eq(self, &proc.ctx) {
            pr_err!("Context::deregister_process called on the wrong context.");
            return;
        }
        // SAFETY: We just checked that this is the right list.
        unsafe {
            self.manager.lock().all_procs.remove(proc);
        }
    }

    pub(crate) fn get_all_procs(&self) -> Result<Vec<Ref<Process>>> {
        let mut lock = self.manager.lock();

        // TODO: The current cursor API gives me a `&Process` rather than a `&Ref<Process>`, so I
        // can't call clone to get a `Ref<Process>` via a cursor.
        let mut procs = Vec::new();
        while let Some(cur) = lock.all_procs.pop_front() {
            procs.try_push(cur)?;
        }
        for proc in &procs {
            lock.all_procs.push_back(proc.clone());
        }
        Ok(procs)
    }

    pub(crate) fn set_manager_node(&self, node_ref: NodeRef) -> Result {
        let mut manager = self.manager.lock();
        if manager.node.is_some() {
            pr_warn!("BINDER_SET_CONTEXT_MGR already set");
            return Err(EBUSY);
        }
        security::binder_set_context_mgr(&node_ref.node.owner.cred)?;

        // TODO: Get the actual caller id.
        let caller_uid = bindings::kuid_t::default();
        if let Some(ref uid) = manager.uid {
            if uid.val != caller_uid.val {
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

    pub(crate) fn get_manager_node(&self, strong: bool) -> BinderResult<NodeRef> {
        self.manager
            .lock()
            .node
            .as_ref()
            .ok_or_else(BinderError::new_dead)?
            .clone(strong)
    }
}
