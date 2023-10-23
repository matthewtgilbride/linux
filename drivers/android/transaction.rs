// SPDX-License-Identifier: GPL-2.0

use kernel::{
    io_buffer::IoBufferWriter,
    linked_list::Links,
    prelude::*,
    sync::{Arc, SpinLock},
    task::Kuid,
    user_ptr::UserSlicePtrWriter,
};

use crate::{
    allocation::Allocation,
    defs::*,
    error::BinderResult,
    node::{Node, NodeRef},
    process::Process,
    ptr_align,
    thread::Thread,
    DeliverToRead,
};

#[pin_data]
pub(crate) struct Transaction {
    target_node: Option<Arc<Node>>,
    pub(crate) from: Arc<Thread>,
    to: Arc<Process>,
    #[pin]
    allocation: SpinLock<Option<Allocation>>,
    code: u32,
    pub(crate) flags: u32,
    data_size: usize,
    data_address: usize,
    links: Links<dyn DeliverToRead>,
    sender_euid: Kuid,
    txn_security_ctx_off: Option<usize>,
}

impl Transaction {
    pub(crate) fn new(
        node_ref: NodeRef,
        from: &Arc<Thread>,
        tr: &BinderTransactionDataSg,
    ) -> BinderResult<Arc<Self>> {
        let trd = &tr.transaction_data;
        let txn_security_ctx = node_ref.node.flags & FLAT_BINDER_FLAG_TXN_SECURITY_CTX != 0;
        let mut txn_security_ctx_off = if txn_security_ctx { Some(0) } else { None };
        let to = node_ref.node.owner.clone();
        let mut alloc =
            match from.copy_transaction_data(to.clone(), tr, txn_security_ctx_off.as_mut()) {
                Ok(alloc) => alloc,
                Err(err) => {
                    if !err.is_dead() {
                        pr_warn!("Failure in copy_transaction_data: {:?}", err);
                    }
                    return Err(err);
                }
            };
        if trd.flags & TF_ONE_WAY == 0 {
            pr_warn!("Non-oneway transactions are not yet supported.");
            return Err(EINVAL.into());
        }
        if trd.flags & TF_CLEAR_BUF != 0 {
            alloc.set_info_clear_on_drop();
        }
        let target_node = node_ref.node.clone();
        alloc.set_info_target_node(node_ref);
        let data_address = alloc.ptr;

        Ok(Arc::pin_init(pin_init!(Transaction {
            target_node: Some(target_node),
            sender_euid: from.process.cred.euid(),
            from: from.clone(),
            to,
            code: trd.code,
            flags: trd.flags,
            data_size: trd.data_size as _,
            data_address,
            links: Links::new(),
            allocation <- kernel::new_spinlock!(Some(alloc), "Transaction::new"),
            txn_security_ctx_off,
        }))?)
    }

    /// Submits the transaction to a work queue.
    pub(crate) fn submit(self: Arc<Self>) -> BinderResult {
        let process = self.to.clone();
        let mut process_inner = process.inner.lock();
        match process_inner.push_work(self) {
            Ok(()) => Ok(()),
            Err((err, work)) => {
                // Drop work after releasing process lock.
                drop(process_inner);
                drop(work);
                Err(err)
            }
        }
    }
}

impl DeliverToRead for Transaction {
    fn do_work(self: Arc<Self>, _thread: &Thread, writer: &mut UserSlicePtrWriter) -> Result<bool> {
        let mut tr_sec = BinderTransactionDataSecctx::default();
        let tr = tr_sec.tr_data();
        if let Some(target_node) = &self.target_node {
            let (ptr, cookie) = target_node.get_id();
            tr.target.ptr = ptr as _;
            tr.cookie = cookie as _;
        };
        tr.code = self.code;
        tr.flags = self.flags;
        tr.data_size = self.data_size as _;
        tr.data.ptr.buffer = self.data_address as _;
        tr.offsets_size = 0;
        if tr.offsets_size > 0 {
            tr.data.ptr.offsets = (self.data_address + ptr_align(self.data_size)) as _;
        }
        tr.sender_euid = self.sender_euid.into_uid_in_current_ns();
        tr.sender_pid = 0;
        if self.target_node.is_some() && self.flags & TF_ONE_WAY == 0 {
            // Not a reply and not one-way.
            tr.sender_pid = self.from.process.task.pid_in_current_ns();
        }
        let code = if self.target_node.is_none() {
            BR_REPLY
        } else {
            if self.txn_security_ctx_off.is_some() {
                BR_TRANSACTION_SEC_CTX
            } else {
                BR_TRANSACTION
            }
        };

        // Write the transaction code and data to the user buffer.
        writer.write(&code)?;
        if let Some(off) = self.txn_security_ctx_off {
            tr_sec.secctx = (self.data_address + off) as u64;
            writer.write(&tr_sec)?;
        } else {
            writer.write(&*tr)?;
        }

        // It is now the user's responsibility to clear the allocation.
        let alloc = self.allocation.lock().take();
        if let Some(alloc) = alloc {
            alloc.keep_alive();
        }

        Ok(false)
    }

    fn cancel(self: Arc<Self>) {}

    fn get_links(&self) -> &Links<dyn DeliverToRead> {
        &self.links
    }

    fn should_sync_wakeup(&self) -> bool {
        self.flags & TF_ONE_WAY == 0
    }
}
