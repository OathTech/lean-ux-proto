import Leanux.Proofs.WG.Origins.OwnerDeferred
import Leanux.Proofs.WG.Origins.OwnerReceive
import Leanux.Proofs.WG.Origins.CurrentRemaining

/-! Owner bounds and positional checks through the existing traffic observers.
Receive allocation uses the actual input allocation journal; deferred work and
inline polls retain their committed prefixes, including every reached Stop. -/
namespace Leanux.Proofs.WG.OwnerTraffic
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins CurrentEnvironment

private theorem lift_store (a : Leanux.M α) (frame : SameProductStore a) :
    OwnerChecks.Preserves (liftPrefix a) :=
  (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEnvironment.«0».Leanux.Proofs.WG.OwnerEnvironment.lift_store)
    a frame

private theorem multicast (family addr : Nat) :
    OwnerChecks.Preserves (RxHistory.audit (xmitMulticastLoopAudit family addr)) := by
  have owner : OwnerAudited.Audited (xmitMulticastLoopAudit family addr) := by
    unfold xmitMulticastLoopAudit
    repeat' first
      | (owner_audit_at loopbackSendPrefix
         exact (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerAudited.«0».Leanux.Proofs.WG.OwnerAudited.native_audit)
           _ _ (loopbackSendPrefix_erases _ _)
           (OwnerControls.store _ (loopbackSend_kernel _ _)))
      | owner_audit_steps
  exact OwnerAudited.join _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRemaining.«0».Leanux.Proofs.WG.CurrentRemaining.multicast) family addr).2
    (RxHistory.audit_preserves _ (xmitMulticastLoopAudit_preserves family addr)) owner.2

/-- The body remains an arbitrary product observer with its explicit contract. -/
theorem runWorker (worker : Worker) (body : RxHistory.Obs Unit)
    (hb : OwnerChecks.Preserves body) : OwnerChecks.Preserves (runWorkerPrefix worker body) :=
  runWorkerPrefix_preserves (fun _ _ hi => hi.safe) OwnerWorkers.store worker hb

theorem handshakeReceiveWorker : OwnerChecks.Preserves RxHistory.handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    OwnerHandshake.receiveStep (OwnerEnvironment.nestedResched _) _ _

private theorem transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) := by
  apply OwnerChecks.native_mixed _ _ (wgXmitPrefix_erases _ _ _ _)
    (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    (Retaining.wgXmit_material _ _ _ _) (CurrentStack.wgXmit_preserves _ _ _ _)
  intro history
  exact hoare_consequence (OwnerStack.wgXmit_preserves family addr packets mtu)
    (fun _ hi => hi.2) (fun _ _ hi => hi)

macro "owner_traffic_steps" : tactic => `(tactic| first
  | unfold OwnerChecks.Preserves
  | (current_env_at wgReceivePrefix; exact OwnerReceive.wgReceive_checked _ _)
  | (current_env_at wgXmitPrefix; exact transmit _ _ _ _)
  | (environment_at "xmitMulticastLoopAudit"; exact multicast _ _)
  | (current_env_at RxHistory.runCryptWorkers; exact OwnerDeferred.runCryptWorkers)
  | (current_env_at RxHistory.runSendWorkers; exact OwnerDeferred.runSendWorkers)
  | (current_env_at RxHistory.schedule; exact OwnerEnvironment.schedule _)
  | (current_env_at RxHistory.pollScheduledInline; exact OwnerWorkers.pollScheduledInline)
  | (current_env_at runWorkerPrefix; apply runWorker)
  | (current_env_at requireNotPending
     exact lift_store _ (liftWG_sameProductStore _ (SameView.pure _ _)))
  | (current_env_at Env.fixtureSend
     exact lift_store _ (fun initial => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (current_env_at getRouting
     exact lift_store _ (by apply (ProjectedAction.iff_run _ _ _).mpr; intro w x v hr; cases hr; rfl))
  | (current_env_at Env.senderSource; exact lift_store _ (senderSource_sameKernel _ _ _ _))
  | (current_env_at Env.xmitPackets; exact lift_store _ (xmitPackets_sameKernel _ _ _ _))
  | (current_env_at liftM
     exact lift_store _ (fun initial => productRouting_spec _ (fun s => s = initial)))
  | (current_env_at ite; apply PrefixPreserves.ite)
  | owner_deferred_timer_steps)

theorem inject (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    OwnerChecks.Preserves (RxHistory.inject family port msg tos ll dest) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.inject
  repeat' owner_traffic_steps

theorem afterBatch : OwnerChecks.Preserves RxHistory.afterBatch := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.afterBatch
  repeat' owner_traffic_steps

theorem flood (count port family : Nat) (messages : List (List UInt8)) :
    OwnerChecks.Preserves (RxHistory.flood count port family messages) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.flood
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch)
    | owner_traffic_steps

theorem batchItem (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    OwnerChecks.Preserves (RxHistory.batchItem d cqes item) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.batchItem
  repeat' owner_traffic_steps

theorem batch (items : List Env.BatchItem) : OwnerChecks.Preserves (RxHistory.batch items) := by
  change PrefixPreserves OwnerChecks.Inv OwnerChecks.Safe _
  unfold RxHistory.batch
  repeat' first
    | (current_env_at RxHistory.afterBatch; exact afterBatch)
    | (current_env_at RxHistory.batchItem; exact batchItem _ _ _)
    | owner_traffic_steps

end Leanux.Proofs.WG.OwnerTraffic
