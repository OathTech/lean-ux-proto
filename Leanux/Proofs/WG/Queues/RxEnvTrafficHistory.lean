import Leanux.Proofs.WG.Queues.RxEnvWorkersHistory
import Leanux.Proofs.WG.Lifetimes.EnvTrafficAudit

/-! Actual environment ingress and every exact flood producer retain nested receive-worker
reschedules. Poll-free ingress steps are focused; every reached reschedule uses
the committed stamped scheduler, with the same prior audit and probe history. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- The original worker callback is reached only after a handled receive item. -/
def handshakeReceiveWorker : Obs Unit :=
  workerLoopPrefix .receiveWorker none Origins.HistoryAdapters.receiveStep (nestedResched .receiveWorker)
    (MAX_QUEUED_INCOMING_HANDSHAKES + 1) "the handshake queue did not drain"

theorem handshakeReceiveWorker_erases : ErasesPrefix handshakeReceiveWorker
    (Leanux.WG.handshakeReceiveWorker (Env.nestedResched .receiveWorker)) :=
  workerLoopPrefix_erases _ _ Origins.HistoryAdapters.receiveStep_erases
    (nestedResched_erases _) _ _

theorem handshakeReceiveWorker_preserves : PrefixPreserves BoundaryInv BoundarySafe handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    Origins.HistoryAdapters.receiveStep_preserves (nestedResched_preserves _) _ _

theorem handshakeReceiveWorker_projects : ProjectsUnder AuditInv auditEvent handshakeReceiveWorker
    (handshakeReceiveWorkerAudit (nestedReschedAudit .receiveWorker)) := by
  have hs : PrefixPreserves AllocationInv LifetimeEvent.Safe receiveStepPrefix :=
    HandshakeReceiveCall.allocation .step
  have hp := Origins.HistoryAdapters.receiveStep_projects
  have ha := auditFocus_preserves hs
  unfold handshakeReceiveWorker handshakeReceiveWorkerAudit workerLoopPrefix workerIterPrefix
  repeat' first
    | exact hp
    | exact ha
    | with_reducible exact nestedResched_projects _
    | with_reducible exact nestedReschedAudit_preserves _
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | exact auditLift_kernel _ (by intro w x v hr; cases hr <;> rfl)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply projectsUnder_range
    | with_reducible apply projectsUnder_bind
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

def inject (family port : Nat) (msg : List UInt8) (tos : Nat := 0) (ll : Bool := false) (dest : Nat := 0) : Obs Int := do
  if (← liftPrefix get).foreignCreator then
    if (← liftPrefix get).netnsCHolders.isEmpty then liftPrefix (unsupported "wg_inject after wg_netns_close (no socket in the creating namespace)")
    if dest == 1 then liftPrefix (unsupported "wg_inject to wg0's address from the creating namespace (unroutable)")
  let some d := (← liftPrefix getK).wg | liftPrefix (unsupported "a datagram to a port other than wg0's (no wg0)")
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a datagram to a port other than wg0's")
  for pid in d.peerList do liftPrefix (requireNotPending pid "receiving while a handshake is queued")
  liftPrefix fixtureSend
  let src ← liftPrefix (senderSource family dest tos ll)
  runWorkerPrefix .netRx (mixed (wgReceivePrefix msg src))
  runCryptWorkers
  let d ← liftPrefix getDev
  mixed (requireDrainedPrefix "the datagram queued"
    [!d.handshakeQueue.empty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  return msg.length

macro "rx_env_traffic_erasure" : tactic => `(tactic|
  repeat' first
    | with_reducible exact mixed_erases (wgReceivePrefix_erases _ _)
    | with_reducible exact mixed_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact runCryptWorkers_erases
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible exact handshakeReceiveWorker_erases
    | with_reducible exact audit_erases (erasesPrefix_lift _)
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

macro "rx_env_traffic_preservation" : tactic => `(tactic|
  repeat' first
    | with_reducible exact mixed_preserves (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible exact mixed_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact runCryptWorkers_preserves
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible exact handshakeReceiveWorker_preserves
    | with_reducible exact boundaryLift_kernel _ (hidden_sameKernel _)
    | with_reducible exact boundaryLift_kernel _ (senderSource_sameKernel _ _ _ _)
    | with_reducible exact boundaryLift_kernel _ fixtureSend_sameKernel
    | with_reducible exact boundaryLift_kernel _ getDev_sameKernel
    | with_reducible exact boundaryLift_kernel _ deliverSent_sameKernel
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact boundaryLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

macro "rx_env_traffic_projection" : tactic => `(tactic|
  repeat' first
    | with_reducible exact mixed_projects (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible exact mixed_projects (requireDrainedPrefix_allocation _ _)
    | with_reducible exact runCryptWorkers_projects
    | with_reducible apply runWorker_projects
    | with_reducible exact handshakeReceiveWorker_projects
    | with_reducible exact projectsUnder_lift _ _
    | with_reducible exact projectsUnder_pure _ _
    | with_reducible apply projectsUnder_forIn
    | with_reducible apply projectsUnder_bind
    | env_traffic_preservation
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem inject_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (inject family port msg tos ll dest) (Env.inject family port msg tos ll dest) := by
  unfold inject Env.inject
  rx_env_traffic_erasure

theorem inject_preserves (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves BoundaryInv BoundarySafe (inject family port msg tos ll dest) := by
  unfold inject
  rx_env_traffic_preservation

theorem inject_projects (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ProjectsUnder AuditInv auditEvent (inject family port msg tos ll dest) (injectAudit family port msg tos ll dest) := by
  unfold inject injectAudit
  rx_env_traffic_projection

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
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0])
  liftPrefix deliverSent

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

def flood (count port family : Nat) (messages : List (List UInt8)) : Obs Int := do
  let some d := (← liftPrefix getK).wg | liftPrefix (unsupported "a flood to a port other than wg0's (no wg0)")
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a flood to a port other than wg0's")
  for pid in d.peerList do liftPrefix (requireNotPending pid "a flood while a handshake is queued")
  let invalid : List UInt8 := [1] ++ List.replicate 115 0 ++ List.replicate 16 0xff ++ List.replicate 16 0
  let src ← liftPrefix (senderSource family 0)
  for msg in messages ++ List.replicate count invalid do
    liftPrefix fixtureSend
    runWorkerPrefix .netRx do
      mixed (wgReceivePrefix msg src)
      pollScheduledInline
  afterBatch
  let d ← liftPrefix getDev
  mixed (requireDrainedPrefix "the flood queued" [!d.handshakeQueue.empty, d.handshakeQueueLen != 0])
  return 0

theorem flood_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (flood count port family messages) (Env.flood count port family messages) := by
  unfold flood Env.flood
  repeat' first
    | with_reducible exact afterBatch_erases
    | with_reducible exact pollScheduledInline_erases
    | rx_env_traffic_erasure

theorem flood_preserves (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves BoundaryInv BoundarySafe (flood count port family messages) := by
  unfold flood
  repeat' first
    | with_reducible exact afterBatch_preserves
    | with_reducible exact pollScheduledInline_preserves
    | rx_env_traffic_preservation

theorem flood_projects (count port family : Nat) (messages : List (List UInt8)) :
    ProjectsUnder AuditInv auditEvent (flood count port family messages) (floodAudit count port family messages) := by
  have body_safe (msg src) : PrefixPreserves AuditInv AuditSafe
      (do auditFocus (wgReceivePrefix msg src); pollScheduledInlineAudit) :=
    PrefixPreserves.bind
      (auditFocus_preserves (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress msg src))
      (fun _ => pollScheduledInlineAudit_preserves)
  have body_projects (msg src) : ProjectsUnder AuditInv auditEvent
      (do mixed (wgReceivePrefix msg src); pollScheduledInline)
      (do auditFocus (wgReceivePrefix msg src); pollScheduledInlineAudit) :=
    projectsUnder_bind
      (mixed_projects (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress msg src))
      (auditFocus_preserves (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress msg src))
      (fun _ => pollScheduledInline_projects)
  have producer_projects (msg src) := runWorker_projects .netRx (body_projects msg src) (body_safe msg src)
  have producer_safe (msg src) := runWorkerPrefix_preserves
    (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he) .netRx (body_safe msg src)
  unfold flood floodAudit
  repeat' first
    | exact producer_projects _ _
    | exact producer_safe _ _
    | exact afterBatch_projects
    | exact afterBatchAudit_preserves
    | exact mixed_projects (requireDrainedPrefix_allocation _ _)
    | exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | exact projectsUnder_lift _ _
    | exact projectsUnder_pure _ _
    | exact auditLift_kernel _ (senderSource_sameKernel _ _ _ _)
    | exact auditLift_kernel _ fixtureSend_sameKernel
    | exact auditLift_kernel _ getDev_sameKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | apply projectsUnder_forIn
    | apply projectsUnder_bind
    | apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | apply PrefixPreserves.bind
    | (split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (intro x; try dsimp only)

end Leanux.Proofs.WG.Queues.RxHistory
