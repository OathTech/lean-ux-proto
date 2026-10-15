import Leanux.Proofs.WG.Queues.RxEnvTrafficHistory
import Leanux.Proofs.WG.Lifetimes.EnvBatchAudit

/-! Original batch items and deferred processing retain actual poll placement.
Ingress and its inline poll share one NET_RX section; CQEs and captured device
scalars follow the original source on every normal or failed prefix. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

def afterBatch : Obs Unit := do
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  if (← liftPrefix get).hidden.isNone then
    runCryptWorkers
    runSendWorkers
    return
  for _ in [0:(← liftPrefix recordBudget)] do
    schedule
    if (← liftPrefix peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← liftPrefix getDev).sendWorkQueue.isEmpty then
      audit runOneSendWorkerAudit
    else break
  let d ← liftPrefix getDev
  mixed (requireDrainedPrefix "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty])
  liftPrefix deliverSent

def batchItem (d : Device) (cqes : List Int) (item : BatchItem) : Obs (ForInStep (List Int)) := do
  let mut cqes := cqes
  match item with
  | .inject family port msg =>
    if port != d.incomingPort then liftPrefix (unsupported "a batch datagram to a port other than wg0's")
    liftPrefix fixtureSend
    let src ← liftPrefix (senderSource family 0)
    runWorkerPrefix .netRx do
      mixed (wgReceivePrefix msg src)
      pollScheduledInline
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
        audit (xmitMulticastLoopAudit family addr)
        let ret ← mixed (wgXmitPrefix family addr pkts mtu)
        cqes := cqes ++ [if ret == 0 then (payload.length : Int) else ret]
  return .yield cqes

def batch (items : List BatchItem) : Obs Int := do
  let some d := (← liftPrefix getK).wg | liftPrefix (unsupported "a batch without wg0")
  if !d.running then liftPrefix (unsupported "a batch with wg0 down")
  for pid in d.peerList do liftPrefix (requireNotPending pid "a batch while a handshake is queued")
  let cqes ← forIn items ([] : List Int) (fun item cqes => batchItem d cqes item)
  liftPrefix (modify fun w => {w with extraOut := [("cqes", Lean.toJson cqes)]})
  afterBatch
  return items.length

theorem afterBatch_erases : ErasesPrefix afterBatch (Env.afterBatch) := by
  unfold afterBatch Env.afterBatch
  repeat' first
    | with_reducible exact runCryptWorkers_erases
    | with_reducible exact runSendWorkers_erases
    | with_reducible exact audit_erases runOneSendWorkerAudit_erases
    | with_reducible exact schedule_erases _
    | with_reducible exact pollScheduledInline_erases
    | with_reducible exact audit_erases (xmitMulticastLoopAudit_erases _ _)
    | with_reducible exact mixed_erases (wgXmitPrefix_erases _ _ _ _)
    | with_reducible apply erasesPrefix_range
    | rx_env_traffic_erasure
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterBatch_preserves : PrefixPreserves BoundaryInv BoundarySafe afterBatch := by
  unfold afterBatch
  repeat' first
    | with_reducible exact runSendWorkers_preserves
    | with_reducible exact audit_preserves _ runOneSendWorkerAudit_preserves
    | with_reducible exact schedule_preserves _
    | with_reducible exact pollScheduledInline_preserves
    | with_reducible exact audit_preserves _ (xmitMulticastLoopAudit_preserves _ _)
    | with_reducible exact mixed_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact boundaryLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact boundaryLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact boundaryLift_kernel _ recordBudget_sameKernel
    | with_reducible exact boundaryLift_kernel _ peekNextSite_sameKernel
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | rx_env_traffic_preservation
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem afterBatch_projects : ProjectsUnder AuditInv auditEvent afterBatch afterBatchAudit := by
  unfold afterBatch afterBatchAudit
  repeat' first
    | with_reducible exact runSendWorkers_projects
    | with_reducible exact audit_projects runOneSendWorkerAudit_preserves
    | with_reducible exact schedule_projects _
    | with_reducible exact pollScheduledInline_projects
    | with_reducible exact audit_projects (xmitMulticastLoopAudit_preserves _ _)
    | with_reducible exact mixed_projects (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible apply projectsUnder_range
    | with_reducible exact runCryptWorkers_projects
    | with_reducible exact mixed_projects (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible exact mixed_projects (requireDrainedPrefix_allocation _ _)
    | with_reducible apply runWorker_projects
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact pollScheduledInlineAudit_preserves
    | with_reducible exact xmitMulticastLoopAudit_preserves _ _
    | with_reducible exact auditFocus_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact auditFocus_preserves (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact auditLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ (senderSource_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ fixtureSend_sameKernel
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply projectsUnder_forIn
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem batchItem_erases (d : Device) (cqes : List Int) (item : BatchItem) : ErasesPrefix (batchItem d cqes item) (Environment.batchItemSource d cqes item) := by
  unfold batchItem Environment.batchItemSource
  repeat' first
    | with_reducible exact afterBatch_erases
    | with_reducible exact runCryptWorkers_erases
    | with_reducible exact runSendWorkers_erases
    | with_reducible exact audit_erases runOneSendWorkerAudit_erases
    | with_reducible exact schedule_erases _
    | with_reducible exact pollScheduledInline_erases
    | with_reducible exact audit_erases (xmitMulticastLoopAudit_erases _ _)
    | with_reducible exact mixed_erases (wgXmitPrefix_erases _ _ _ _)
    | with_reducible apply erasesPrefix_range
    | rx_env_traffic_erasure
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem batchItem_preserves (d : Device) (cqes : List Int) (item : BatchItem) : PrefixPreserves BoundaryInv BoundarySafe (batchItem d cqes item) := by
  unfold batchItem
  repeat' first
    | with_reducible exact afterBatch_preserves
    | with_reducible exact runSendWorkers_preserves
    | with_reducible exact audit_preserves _ runOneSendWorkerAudit_preserves
    | with_reducible exact schedule_preserves _
    | with_reducible exact pollScheduledInline_preserves
    | with_reducible exact audit_preserves _ (xmitMulticastLoopAudit_preserves _ _)
    | with_reducible exact mixed_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact boundaryLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact boundaryLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact boundaryLift_kernel _ recordBudget_sameKernel
    | with_reducible exact boundaryLift_kernel _ peekNextSite_sameKernel
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | rx_env_traffic_preservation
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem batchItem_projects (d : Device) (cqes : List Int) (item : BatchItem) : ProjectsUnder AuditInv auditEvent (batchItem d cqes item) (batchItemAudit d cqes item) := by
  unfold batchItem batchItemAudit
  repeat' first
    | with_reducible exact afterBatch_projects
    | with_reducible exact afterBatchAudit_preserves
    | with_reducible exact runSendWorkers_projects
    | with_reducible exact audit_projects runOneSendWorkerAudit_preserves
    | with_reducible exact schedule_projects _
    | with_reducible exact pollScheduledInline_projects
    | with_reducible exact audit_projects (xmitMulticastLoopAudit_preserves _ _)
    | with_reducible exact mixed_projects (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible apply projectsUnder_range
    | with_reducible exact runCryptWorkers_projects
    | with_reducible exact mixed_projects (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible exact mixed_projects (requireDrainedPrefix_allocation _ _)
    | with_reducible apply runWorker_projects
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact pollScheduledInlineAudit_preserves
    | with_reducible exact xmitMulticastLoopAudit_preserves _ _
    | with_reducible exact auditFocus_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact auditFocus_preserves (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact auditLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ (senderSource_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ fixtureSend_sameKernel
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply projectsUnder_forIn
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem batch_erases (items : List BatchItem) : ErasesPrefix (batch items) (Env.batch items) := by
  rw [← Environment.batchSource_eq]
  unfold batch Environment.batchSource
  repeat' first
    | with_reducible exact afterBatch_erases
    | with_reducible exact batchItem_erases _ _ _
    | with_reducible exact runCryptWorkers_erases
    | with_reducible exact runSendWorkers_erases
    | with_reducible exact audit_erases runOneSendWorkerAudit_erases
    | with_reducible exact schedule_erases _
    | with_reducible exact pollScheduledInline_erases
    | with_reducible exact audit_erases (xmitMulticastLoopAudit_erases _ _)
    | with_reducible exact mixed_erases (wgXmitPrefix_erases _ _ _ _)
    | with_reducible apply erasesPrefix_range
    | rx_env_traffic_erasure
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem batch_preserves (items : List BatchItem) : PrefixPreserves BoundaryInv BoundarySafe (batch items) := by
  unfold batch
  repeat' first
    | with_reducible exact afterBatch_preserves
    | with_reducible exact batchItem_preserves _ _ _
    | with_reducible exact runSendWorkers_preserves
    | with_reducible exact audit_preserves _ runOneSendWorkerAudit_preserves
    | with_reducible exact schedule_preserves _
    | with_reducible exact pollScheduledInline_preserves
    | with_reducible exact audit_preserves _ (xmitMulticastLoopAudit_preserves _ _)
    | with_reducible exact mixed_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact boundaryLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact boundaryLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact boundaryLift_kernel _ recordBudget_sameKernel
    | with_reducible exact boundaryLift_kernel _ peekNextSite_sameKernel
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | rx_env_traffic_preservation
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

theorem batch_projects (items : List BatchItem) : ProjectsUnder AuditInv auditEvent (batch items) (batchAudit items) := by
  unfold batch batchAudit
  repeat' first
    | with_reducible exact afterBatch_projects
    | with_reducible exact afterBatchAudit_preserves
    | with_reducible exact batchItem_projects _ _ _
    | with_reducible exact batchItemAudit_preserves _ _ _
    | with_reducible exact runSendWorkers_projects
    | with_reducible exact audit_projects runOneSendWorkerAudit_preserves
    | with_reducible exact schedule_projects _
    | with_reducible exact pollScheduledInline_projects
    | with_reducible exact audit_projects (xmitMulticastLoopAudit_preserves _ _)
    | with_reducible exact mixed_projects (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible apply projectsUnder_range
    | with_reducible exact runCryptWorkers_projects
    | with_reducible exact mixed_projects (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible exact mixed_projects (requireDrainedPrefix_allocation _ _)
    | with_reducible apply runWorker_projects
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact pollScheduledInlineAudit_preserves
    | with_reducible exact xmitMulticastLoopAudit_preserves _ _
    | with_reducible exact auditFocus_preserves (wgXmitPrefix_preserves allocationAmbient allocationTx allocationWgXmit _ _ _ _)
    | with_reducible exact auditFocus_preserves (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact auditLift_kernel _ (routeLookup_sameKernel _ _ _)
    | with_reducible exact auditLift_kernel _ (xmitPackets_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ (senderSource_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ fixtureSend_sameKernel
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply projectsUnder_forIn
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, BatchItem.inject.injEq, BatchItem.xmit.injEq, Except.ok.injEq, Except.error.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.Queues.RxHistory
