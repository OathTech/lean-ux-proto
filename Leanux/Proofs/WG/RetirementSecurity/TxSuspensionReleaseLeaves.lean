import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionWake

/-! Native inode, eventfd and final-file release leaves preserve actual
suspended worker records through their declared ambient effects. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
open Leanux Leanux.Proofs.Framing Lifetimes Queues

theorem eventfd_of (f : File) : Keeps (eventfdCtxOf f) := by
  nested_suspension_source [eventfdCtxOf] using [invariant]

theorem eventfd_free (id : CtxId) : Keeps (eventfdFreeCtx id) := by
  nested_suspension_source [eventfdFreeCtx] using [get_ctx,invariant,compare,free_ctx]

theorem eventfd_put (id : CtxId) : Keeps (eventfdCtxPut id) := by
  nested_suspension_source [eventfdCtxPut] using [get_ctx,set_ctx,branch,refcount_dec,eventfd_free]

theorem eventfd_release (fid : FileId) : Keeps (eventfdRelease fid) := by
  nested_suspension_source [eventfdRelease] using [get_file,eventfd_of,wake_poll,eventfd_put]

theorem inode_chr (ino : Option InodeId) : Keeps (inodeIsChr ino) := by
  nested_suspension_source [inodeIsChr] using [get_inode,invariant]

theorem inode_readcount_dec (ino : Option InodeId) : Keeps (inodeReadcountDec ino) := by
  nested_suspension_source [inodeReadcountDec] using [get_inode,set_inode,invariant,unsupported,compare]

theorem file_access_put (f : File) : Keeps (putFileAccess f) := by
  nested_suspension_source [putFileAccess] using [compare,inode_readcount_dec,unsupported]

theorem pipe_inode_put (id : PipefsInodeId) : Keeps (iputPipefs id) := by
  nested_suspension_source [iputPipefs] using [get_inode,set_inode,invariant,unsupported,branch]

theorem pipe_dentry_put (id : PipefsInodeId) : Keeps (dputPipefs id) := by
  nested_suspension_source [dputPipefs] using [get_inode,set_inode,invariant,pipe_inode_put]

theorem fops (ops : Option FopsId) : Keeps (fopsOf ops) := by
  nested_suspension_source [fopsOf] using [invariant]

theorem iput (last : Bool) : Keeps (iputReport last : FS.M Unit) :=
  lift (TxSuspension.iput last)

theorem device_work (worker : Worker) : Keeps (queueDeviceWork worker : FS.M Unit) := by
  apply ambient
  unfold AmbientM.queueDeviceWork
  intro initial
  change Preserves (fun s : Ambient=>s.suspended=initial) _
  have peek:=TxSuspension.peek_queued_ambient worker 0 initial
  have record:=TxSuspension.record_queued_ambient worker 0 initial
  repeat' first
    | (rx_retention_head AmbientM.peekQueuedUnit; exact peek)
    | (rx_retention_head AmbientM.recordQueued; exact record)
    | (rx_retention_head MonadState.get
       exact hoare_consequence (hoare_get _) (fun _ h=>h) (fun _ _ h=>h.2))
    | (rx_retention_head _root_.modify; apply hoare_modify; intro w h; exact h)
    | (rx_retention_head AmbientM.unsupported
       apply (hoare_iff_run _ _ _).mpr
       intro w result v before run
       cases run)
    | routing_tx_step

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension.Nested
