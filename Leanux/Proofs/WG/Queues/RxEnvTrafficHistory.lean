import Leanux.Proofs.WG.Queues.RxEnvWorkersHistory
import Leanux.Proofs.WG.Lifetimes.EnvTrafficAudit

/-! Actual environment ingress and both flood modes retain nested receive-worker
reschedules. Poll-free ingress steps are focused; every reached reschedule uses
the committed stamped scheduler, with the same prior audit and probe history. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

/-- The original worker callback is reached only after a handled receive item. -/
def handshakeReceiveWorker : Obs Unit :=
  workerLoopPrefix .receiveWorker none (mixed receiveStepPrefix) (nestedResched .receiveWorker)
    MAX_QUEUED_INCOMING_HANDSHAKES "the handshake queue did not drain"

theorem handshakeReceiveWorker_erases : ErasesPrefix handshakeReceiveWorker
    (Leanux.WG.handshakeReceiveWorker (Env.nestedResched .receiveWorker)) :=
  workerLoopPrefix_erases _ _ (mixed_erases receiveStepPrefix_erases)
    (nestedResched_erases _) _ _

theorem handshakeReceiveWorker_preserves : PrefixPreserves BoundaryInv BoundarySafe handshakeReceiveWorker :=
  workerLoopPrefix_preserves _ _ (fun _ _ hi => hi.safe)
    (mixed_preserves (HandshakeReceiveCall.allocation .step)) (nestedResched_preserves _) _ _

theorem handshakeReceiveWorker_projects : ProjectsUnder AuditInv auditEvent handshakeReceiveWorker
    (handshakeReceiveWorkerAudit (nestedReschedAudit .receiveWorker)) := by
  have hs : PrefixPreserves AllocationInv LifetimeEvent.Safe receiveStepPrefix :=
    HandshakeReceiveCall.allocation .step
  have hp := mixed_projects hs
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
    [!d.handshakeQueue.isEmpty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  return msg.length

def flood (count port family : Nat) (messages : List (List UInt8)) : Obs Int := do
  let some d := (← liftPrefix getK).wg | liftPrefix (unsupported "a flood to a port other than wg0's (no wg0)")
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a flood to a port other than wg0's")
  if (← liftPrefix get).hidden.isNone then
    liftPrefix (modify fun w => {w with lastUnderLoad := some 0})
    return 0
  let startW := (HiddenSite.sectionStart .receiveWorker).info.id
  let stopW := (HiddenSite.sectionStop .receiveWorker).info.id
  let startRx := (HiddenSite.sectionStart .netRx).info.id
  let stopRx := (HiddenSite.sectionStop .netRx).info.id
  let cuts := [startRx, stopRx, (HiddenSite.ipIdentKey).info.id, (HiddenSite.ipIdentReserve).info.id,
    (HiddenSite.flowHashSecret).info.id, (HiddenSite.udpPortDraw).info.id,
    (HiddenSite.queued .receiveWorker).info.id]
  let _ ← audit (liftPrefix (discardFloodRecords startW cuts))
  _ ← liftPrefix (hidden (.sectionStart .receiveWorker))
  let src ← liftPrefix (senderSource family 0)
  if (← liftPrefix get).floodExact then
    let invalid : List UInt8 := [1] ++ List.replicate 115 0 ++ List.replicate 16 0xff ++ List.replicate 16 0
    audit (liftPrefix (modifyDev (floodQueue (messages ++ List.replicate count invalid) src (messages.length + count))))
    handshakeReceiveWorker
    _ ← liftPrefix (hidden (.sectionStop .receiveWorker))
    liftPrefix deliverSent
    return 0
  audit (liftPrefix (modifyDev (floodQueue messages src (messages.length + count))))
  handshakeReceiveWorker
  let (last, crossed) ← liftPrefix (floodTailEffect stopW cuts (← liftPrefix get).lastUnderLoad)
  liftPrefix (modify fun w => {w with lastUnderLoad := last})
  audit (liftPrefix (modifyDev fun d => {d with handshakeQueueLen := 0}))
  _ ← liftPrefix (hidden (.sectionStop .receiveWorker))
  if messages.isEmpty && !crossed then
    liftPrefix (throw (.hidden "the flood did not cross the under_load threshold (no under_load record)"))
  liftPrefix deliverSent
  return 0

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
    | with_reducible exact audit_preserves _ (auditFloodQueue_preserves _ _ _)
    | with_reducible exact audit_preserves _ auditFloodReset_preserves
    | with_reducible exact audit_preserves _ (auditLift_wgKernel _ (KernelFrames.discardFloodRecords_sameWGKernel _ _))
    | with_reducible exact boundaryLift_kernel _ (floodTailEffect_sameKernel _ _ _)
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
    | with_reducible exact audit_projects (auditFloodQueue_preserves _ _ _)
    | with_reducible exact audit_projects auditFloodReset_preserves
    | with_reducible exact audit_projects (auditLift_wgKernel _ (KernelFrames.discardFloodRecords_sameWGKernel _ _))
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

theorem flood_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (flood count port family messages) (Env.flood count port family messages) := by
  unfold flood Env.flood floodQueue
  simp only [Nat.add_assoc]
  rx_env_traffic_erasure

theorem flood_preserves (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves BoundaryInv BoundarySafe (flood count port family messages) := by
  unfold flood
  rx_env_traffic_preservation

theorem flood_projects (count port family : Nat) (messages : List (List UInt8)) :
    ProjectsUnder AuditInv auditEvent (flood count port family messages) (floodAudit count port family messages) := by
  unfold flood floodAudit
  rx_env_traffic_projection

end Leanux.Proofs.WG.Queues.RxHistory
