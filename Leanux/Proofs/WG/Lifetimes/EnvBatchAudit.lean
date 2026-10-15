import Leanux.Proofs.WG.Lifetimes.EnvTrafficAudit
import Leanux.Proofs.WG.Environment.BatchSource

/-! Original batch submission and its deferred continuation. Per-item CQEs,
captured device scalars, inline polling and scheduler probes retain their source
order. No successful draining or valid-input premise is used. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing

def batchItemAudit (d : Device) (cqes : List Int) (item : BatchItem) : AuditM (ForInStep (List Int)) := do
  let mut cqes := cqes
  match item with
  | .inject family port msg =>
    if port != d.incomingPort then liftPrefix (unsupported "a batch datagram to a port other than wg0's")
    liftPrefix fixtureSend
    let src ← liftPrefix (senderSource family 0)
    runWorkerPrefix .netRx do
      auditFocus (wgReceivePrefix msg src)
      pollScheduledInlineAudit
    cqes := cqes ++ [(msg.length : Int)]
  | .xmit family addr payload opts =>
    match ← liftPrefix (routeLookup family 0 addr) with
    | .error err => cqes := cqes ++ [err]
    | .ok r =>
      if r.dev != WG0_IFINDEX then liftPrefix (unsupported "a batch transmit to a local address (not into wg0)")
      if (family == 4 && !d.inet4Dev) || (family == 6 && !d.inet6Dev) then
        liftPrefix (unsupported "a transmit after an MTU change took the family's routes into wg0 down")
      liftPrefix fixtureSend
      match ← liftPrefix (xmitPackets family addr payload opts) with
      | .error e => cqes := cqes ++ [e]
      | .ok (pkts, mtu) =>
        xmitMulticastLoopAudit family addr
        let ret ← auditFocus (wgXmitPrefix family addr pkts mtu)
        cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  return .yield cqes

def batchAudit (items : List BatchItem) : AuditM Int := do
  let some d := (← liftPrefix getK).wg | liftPrefix (unsupported "a batch without wg0")
  if !d.running then liftPrefix (unsupported "a batch with wg0 down")
  for pid in d.peerList do liftPrefix (requireNotPending pid "a batch while a handshake is queued")
  let cqes ← forIn items ([] : List Int) (fun item cqes => batchItemAudit d cqes item)
  liftPrefix (modify fun w => {w with extraOut := [("cqes", Lean.toJson cqes)]})
  afterBatchAudit
  return items.length

macro "env_batch_erasure" : tactic => `(tactic|
  repeat' first
    | with_reducible exact afterBatchAudit_erases
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact scheduleAudit_erases _
    | with_reducible exact pollScheduledInlineAudit_erases
    | with_reducible exact xmitMulticastLoopAudit_erases _ _
    | with_reducible exact auditFocus_erases (wgXmitPrefix_erases _ _ _ _)
    | with_reducible apply erasesPrefix_range
    | env_traffic_erasure)

macro "env_batch_preservation" : tactic => `(tactic|
  repeat' first
    | with_reducible exact afterBatchAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact pollScheduledInlineAudit_preserves
    | with_reducible exact xmitMulticastLoopAudit_preserves _ _
    | with_reducible exact auditFocus_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact auditLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | env_traffic_preservation)

theorem batchItemAudit_erases (d : Device) (cqes : List Int) (item : BatchItem) : ErasesPrefix (batchItemAudit d cqes item) (Environment.batchItemSource d cqes item) := by
  unfold batchItemAudit Environment.batchItemSource
  repeat' first
    | with_reducible exact afterBatchAudit_erases
    | with_reducible exact pollScheduledInlineAudit_erases
    | with_reducible exact xmitMulticastLoopAudit_erases _ _
    | with_reducible exact auditFocus_erases (wgXmitPrefix_erases _ _ _ _)
    | with_reducible exact auditFocus_erases (wgReceivePrefix_erases _ _)
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem batchItemAudit_preserves (d : Device) (cqes : List Int) (item : BatchItem) : PrefixPreserves AuditInv AuditSafe (batchItemAudit d cqes item) := by
  unfold batchItemAudit
  repeat' first
    | with_reducible exact afterBatchAudit_preserves
    | with_reducible exact pollScheduledInlineAudit_preserves
    | with_reducible exact xmitMulticastLoopAudit_preserves _ _
    | with_reducible exact auditFocus_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact auditFocus_preserves (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact auditLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ (senderSource_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ fixtureSend_sameKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)
theorem batchAudit_erases (items : List BatchItem) : ErasesPrefix (batchAudit items) (Env.batch items) := by
  rw [← Environment.batchSource_eq]
  unfold batchAudit Environment.batchSource
  repeat' first
    | with_reducible exact batchItemAudit_erases _ _ _
    | with_reducible exact afterBatchAudit_erases
    | with_reducible exact pollScheduledInlineAudit_erases
    | with_reducible exact xmitMulticastLoopAudit_erases _ _
    | with_reducible exact auditFocus_erases (wgXmitPrefix_erases _ _ _ _)
    | with_reducible exact auditFocus_erases (wgReceivePrefix_erases _ _)
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem batchAudit_preserves (items : List BatchItem) : PrefixPreserves AuditInv AuditSafe (batchAudit items) := by
  unfold batchAudit
  repeat' first
    | with_reducible exact batchItemAudit_preserves _ _ _
    | with_reducible exact afterBatchAudit_preserves
    | with_reducible exact pollScheduledInlineAudit_preserves
    | with_reducible exact xmitMulticastLoopAudit_preserves _ _
    | with_reducible exact auditFocus_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact auditFocus_preserves (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact auditLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ (senderSource_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ fixtureSend_sameKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Lifetimes
