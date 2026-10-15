import Leanux.Proofs.WG.Lifetimes.EnvControlsAudit
import Leanux.Proofs.WG.Lifetimes.ReceiveIngress

/-! Exact environment ingress, multicast loopback and flood observations. Inline
polling records the complete demanded saved-map scan before effects. Every flood
producer, inline poll and deferred activation follows the original source,
including its partial history when a later record or drain guard fails. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Logged Leanux.Proofs.Framing

def xmitMulticastLoopAudit (family addr : Nat) : AuditM Unit := do
  if multicastLoops family addr then auditFocus (loopbackSendPrefix [] true)
  else if family == 6 && addr / 2 ^ 120 == 0xff then
    liftPrefix (unsupported "an IPv6 multicast destination (whether the IP output loops a copy back depends on wg0's groups)")

def pollScheduledInlinePrefix : MixedM Unit := do
  let d ← liftPrefix getDev
  let pending ← savedPeerFilterMap (fun pid p => if p.napiScheduled then some pid else none) d.peers.toList
  if pending.length > 1 then liftPrefix (unsupported "NAPI polls of several peers in one softirq")
  for pid in pending do
    discard <| rxPollStackPrefix pid NAPI_POLL_WEIGHT

theorem pollScheduledInlinePrefix_erases : ErasesPrefix pollScheduledInlinePrefix Env.pollScheduledInline := by
  unfold pollScheduledInlinePrefix Env.pollScheduledInline
  apply erasesPrefix_bind (erasesPrefix_lift _)
  intro d
  apply erasesPrefix_bind_pure (savedPeerFilterMap_erases _ _)
  dsimp only
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | with_reducible exact rxPollStackPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem pollScheduledInlinePrefix_allocation :
    PrefixPreserves AllocationInv LifetimeEvent.Safe pollScheduledInlinePrefix := by
  apply AmbientContracts.drop (Q := fun _ _ => True)
  unfold pollScheduledInlinePrefix
  apply PrefixEnsures.bind (getDev_saved_spec allocationAmbient (fun _ => True))
  intro d
  apply PrefixEnsures.bind (savedPeerFilterMap_spec allocationAmbient (fun _ => True) _ _)
  intro pending
  apply PrefixEnsures.consequence (show PrefixPreserves AllocationInv LifetimeEvent.Safe _ from ?_)
    (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩)
  simp only [discard, map_const, Function.comp_def, map_eq_pure_bind]
  repeat' first
    | with_reducible exact rxPollStackPrefix_preserves allocationAmbient allocationTx allocationRx allocationWgXmit _ _
    | exact allocation_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact allocation_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

abbrev pollScheduledInlineAudit : AuditM Unit := auditFocus pollScheduledInlinePrefix

theorem pollScheduledInlineAudit_erases : ErasesPrefix pollScheduledInlineAudit Env.pollScheduledInline :=
  auditFocus_erases pollScheduledInlinePrefix_erases

theorem pollScheduledInlineAudit_preserves : PrefixPreserves AuditInv AuditSafe pollScheduledInlineAudit :=
  auditFocus_preserves pollScheduledInlinePrefix_allocation

def injectAudit (family port : Nat) (msg : List UInt8) (tos : Nat := 0) (ll : Bool := false) (dest : Nat := 0) : AuditM Int := do
  if (← liftPrefix get).foreignCreator then
    if (← liftPrefix get).netnsCHolders.isEmpty then liftPrefix (unsupported "wg_inject after wg_netns_close (no socket in the creating namespace)")
    if dest == 1 then liftPrefix (unsupported "wg_inject to wg0's address from the creating namespace (unroutable)")
  let some d := (← liftPrefix getK).wg | liftPrefix (unsupported "a datagram to a port other than wg0's (no wg0)")
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a datagram to a port other than wg0's")
  for pid in d.peerList do liftPrefix (requireNotPending pid "receiving while a handshake is queued")
  liftPrefix fixtureSend
  let src ← liftPrefix (senderSource family dest tos ll)
  runWorkerPrefix .netRx (auditFocus (wgReceivePrefix msg src))
  runCryptWorkersAudit
  let d ← liftPrefix getDev
  auditFocus (requireDrainedPrefix "the datagram queued"
    [!d.handshakeQueue.empty, !d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty])
  return msg.length

def afterBatchAudit : AuditM Unit := do
  liftPrefix (modify fun w => {w with queuedThisCall := []})
  if (← liftPrefix get).hidden.isNone then
    runCryptWorkersAudit
    runSendWorkersAudit
    return
  for _ in [0:(← liftPrefix recordBudget)] do
    scheduleAudit
    if (← liftPrefix peekNextSite) == some (HiddenSite.sectionStart .sendWorker).info.id && !(← liftPrefix getDev).sendWorkQueue.isEmpty then
      runOneSendWorkerAudit
    else break
  let d ← liftPrefix getDev
  auditFocus (requireDrainedPrefix "the batch queued"
    [!d.decryptQueue.empty, !d.encryptQueue.empty, !d.txWorkQueue.isEmpty, !d.sendWorkQueue.isEmpty,
     !d.handshakeQueue.empty, d.handshakeQueueLen != 0])
  liftPrefix deliverSent

macro "env_traffic_erasure" : tactic => `(tactic|
  repeat' first
    | with_reducible exact auditFocus_erases (loopbackSendPrefix_erases _ _)
    | with_reducible exact auditFocus_erases (wgReceivePrefix_erases _ _)
    | with_reducible exact auditFocus_erases (requireDrainedPrefix_erases _ _)
    | with_reducible exact runCryptWorkersAudit_erases
    | with_reducible apply runWorkerPrefix_erases
    | with_reducible apply handshakeReceiveWorkerAudit_erases
    | with_reducible exact nestedReschedAudit_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

macro "env_traffic_preservation" : tactic => `(tactic|
  repeat' first
    | with_reducible exact auditFocus_preserves (AmbientContracts.drop (loopbackSendPrefix_spec allocationAmbient (fun _ => True) _ _))
    | with_reducible exact auditFocus_preserves (wgReceivePrefix_preserves allocationAmbient allocationReceiveIngress _ _)
    | with_reducible exact auditFocus_preserves (requireDrainedPrefix_allocation _ _)
    | with_reducible exact runCryptWorkersAudit_preserves
    | with_reducible apply runWorkerPrefix_preserves (fun _ _ hi => hi.safe) (fun _ _ _ he hi => hi.kernel he)
    | with_reducible apply handshakeReceiveWorkerAudit_preserves
    | with_reducible exact nestedReschedAudit_preserves _
    | with_reducible exact auditLift_kernel _ (hidden_sameKernel _)
    | with_reducible exact auditLift_kernel _ (senderSource_sameKernel _ _ _ _)
    | with_reducible exact auditLift_kernel _ fixtureSend_sameKernel
    | with_reducible exact auditLift_kernel _ getDev_sameKernel
    | with_reducible exact auditLift_kernel _ deliverSent_sameKernel
    | exact auditLift_kernel _ (by intro w x v hr; cases hr; rfl)
    | exact auditLift_kernel _ (by intro w x v hr; cases hr)
    | with_reducible exact PrefixPreserves.pure (fun _ _ hi => hi.safe) _
    | with_reducible apply PrefixPreserves.forIn _ _ _ (fun _ _ hi => hi.safe)
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split; all_goals try simp_all only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq]; all_goals try subst_vars)
    | (with_reducible intro x; try dsimp only))

theorem xmitMulticastLoopAudit_erases (family addr : Nat) :
    ErasesPrefix (xmitMulticastLoopAudit family addr) (Env.xmitMulticastLoop family addr) := by
  unfold xmitMulticastLoopAudit Env.xmitMulticastLoop
  env_traffic_erasure

theorem xmitMulticastLoopAudit_preserves (family addr : Nat) :
    PrefixPreserves AuditInv AuditSafe (xmitMulticastLoopAudit family addr) := by
  unfold xmitMulticastLoopAudit
  env_traffic_preservation

theorem injectAudit_erases (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    ErasesPrefix (injectAudit family port msg tos ll dest) (Env.inject family port msg tos ll dest) := by
  unfold injectAudit Env.inject
  env_traffic_erasure

theorem injectAudit_preserves (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    PrefixPreserves AuditInv AuditSafe (injectAudit family port msg tos ll dest) := by
  unfold injectAudit
  env_traffic_preservation

theorem afterBatchAudit_erases : ErasesPrefix afterBatchAudit Env.afterBatch := by
  unfold afterBatchAudit Env.afterBatch
  repeat' first
    | with_reducible exact runSendWorkersAudit_erases
    | with_reducible exact runOneSendWorkerAudit_erases
    | with_reducible exact scheduleAudit_erases _
    | with_reducible apply erasesPrefix_range
    | env_traffic_erasure

theorem afterBatchAudit_preserves : PrefixPreserves AuditInv AuditSafe afterBatchAudit := by
  unfold afterBatchAudit
  repeat' first
    | with_reducible exact runSendWorkersAudit_preserves
    | with_reducible exact runOneSendWorkerAudit_preserves
    | with_reducible exact scheduleAudit_preserves _
    | with_reducible exact auditLift_kernel _ recordBudget_sameKernel
    | with_reducible exact auditLift_kernel _ peekNextSite_sameKernel
    | with_reducible apply PrefixPreserves.range _ _ _ (fun _ _ hi => hi.safe)
    | env_traffic_preservation

def floodAudit (count port family : Nat) (messages : List (List UInt8)) : AuditM Int := do
  let some d := (← liftPrefix getK).wg | liftPrefix (unsupported "a flood to a port other than wg0's (no wg0)")
  if !d.running || port != d.incomingPort then liftPrefix (unsupported "a flood to a port other than wg0's")
  for pid in d.peerList do liftPrefix (requireNotPending pid "a flood while a handshake is queued")
  let invalid : List UInt8 := [1] ++ List.replicate 115 0 ++ List.replicate 16 0xff ++ List.replicate 16 0
  let src ← liftPrefix (senderSource family 0)
  for msg in messages ++ List.replicate count invalid do
    liftPrefix fixtureSend
    runWorkerPrefix .netRx do
      auditFocus (wgReceivePrefix msg src)
      pollScheduledInlineAudit
  afterBatchAudit
  let d ← liftPrefix getDev
  auditFocus (requireDrainedPrefix "the flood queued" [!d.handshakeQueue.empty, d.handshakeQueueLen != 0])
  return 0

theorem floodAudit_erases (count port family : Nat) (messages : List (List UInt8)) :
    ErasesPrefix (floodAudit count port family messages) (Env.flood count port family messages) := by
  unfold floodAudit Env.flood
  repeat' first
    | with_reducible exact afterBatchAudit_erases
    | with_reducible exact pollScheduledInlineAudit_erases
    | env_traffic_erasure

theorem floodAudit_preserves (count port family : Nat) (messages : List (List UInt8)) :
    PrefixPreserves AuditInv AuditSafe (floodAudit count port family messages) := by
  unfold floodAudit
  repeat' first
    | with_reducible exact afterBatchAudit_preserves
    | with_reducible exact pollScheduledInlineAudit_preserves
    | env_traffic_preservation

end Leanux.Proofs.WG.Lifetimes
