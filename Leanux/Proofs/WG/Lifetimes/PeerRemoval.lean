import Leanux.Proofs.WG.Lifetimes.KeyMaintenance
import Leanux.Proofs.WG.Lifetimes.HandshakeSend
import Leanux.Proofs.WG.Lifetimes.AllowedIpsAccess
import Leanux.Proofs.Logged.PrefixBatch
import Leanux.WG.PeerRemove

/-! Complete peer-removal and inline workqueue-flush observations. Saved queue
and peer-list values are scalar IDs; each actual peer access resolves the current
store. peekUnit/resolveUnit inspect records and World dispatch labels, not peers.
The finite drain keeps its original early returns, placeholder order and Stop.
No pending-work, reference-ownership, distinctness or drain-success premise is
used. These contracts do not cover the enclosing device/environment lifecycle. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def runFlushedSendWorkPrefix (pid : PeerId) : MixedM Unit := do
  liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid})
  let p ← getPeerMixed pid
  if !p.handshakePending then liftPrefix (invariant "queued work without a pending flag")
  setPeerMixed pid {p with handshakePending := false}
  runWorkerPrefix .sendWorker (handshakeSendWorkerPrefix pid)

def runFlushedClearWorkPrefix (pid : PeerId) : MixedM Unit := do
  liftPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid})
  runWorkerPrefix .clearPeerWorker (queuedExpiredZeroKeyMaterialPrefix pid)

def drainHandshakeSendWqPrefix (upTo : Option PeerId) : MixedM Unit := do
  for _ in [0:4096] do
    let d ← liftPrefix getDev
    if d.sendWorkQueue.isEmpty && d.clearWorkQueue.isEmpty then return
    match ← liftPrefix (peekUnit .sendWorker) with
    | some u =>
      let pid ← liftPrefix (resolveUnit .sendWorker u d.sendWorkQueue)
      runFlushedSendWorkPrefix pid
    | none =>
      match ← liftPrefix (peekUnit .clearPeerWorker) with
      | some u =>
        let pid ← liftPrefix (resolveUnit .clearPeerWorker u d.clearWorkQueue)
        runFlushedClearWorkPrefix pid
        if upTo == some pid then return
      | none =>
        if (← liftPrefix get).hidden.isSome then
          liftPrefix (throw (.hidden s!"a flush of handshake_send_wq must run queued work ({d.sendWorkQueue.length} send, {d.clearWorkQueue.length} clear items), but no section names it"))
        match d.sendWorkQueue.head?, d.clearWorkQueue.head? with
        | some pid, _ => runFlushedSendWorkPrefix pid
        | none, some pid =>
          runFlushedClearWorkPrefix pid
          if upTo == some pid then return
        | none, none => return
  liftPrefix (invariant "handshake_send_wq did not drain")

def timersStopPrefix (pid : PeerId) : MixedM Unit := do
  for t in PeerTimer.all do delTimerPrefix pid t
  if (← liftPrefix getDev).clearWorkQueue.contains pid then drainHandshakeSendWqPrefix (some pid)

def peerRemoveAfterDeadPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftPrefix (branch .peerRemoveNotDead !(← getPeerMixed pid).isDead) then
    liftPrefix (unsupported "peer_remove_after_dead: WARN_ON(!peer->is_dead)")
  keypairsClearPrefix pid
  timersStopPrefix pid
  drainHandshakeSendWqPrefix none
  if (← liftPrefix getDev).numPeers == 0 then liftPrefix (invariant "--num_peers below zero")
  liftPrefix (modifyDev fun d => {d with numPeers := d.numPeers - 1})
  peerPutMixed (some pid)

def peerRemovePrefix (peer : Option PeerId) : MixedM Unit := do
  if ← liftPrefix (branch .peerRemoveNull peer.isNone) then return
  let some pid := peer | liftPrefix (invariant "unreachable")
  peerMakeDeadPrefix pid
  peerRemoveAfterDeadPrefix pid

def peerRemoveAllPrefix : MixedM Unit := do
  freeAllowedIpsPrefix
  let dead := (← liftPrefix getDev).peerList
  for pid in dead do
    _ ← liftPrefix (branch .peerRemoveAllIter1 true)
    peerMakeDeadPrefix pid
  _ ← liftPrefix (branch .peerRemoveAllIter1 false)
  for pid in dead do
    _ ← liftPrefix (branch .peerRemoveAllIter2 true)
    peerRemoveAfterDeadPrefix pid
  _ ← liftPrefix (branch .peerRemoveAllIter2 false)

theorem runFlushedSendWorkPrefix_erases (pid : PeerId) :
    ErasesPrefix (runFlushedSendWorkPrefix pid) (runFlushedSendWork pid) := by
  unfold runFlushedSendWorkPrefix runFlushedSendWork runWorkerPrefix
  simp only [show (Worker.sendWorker == .netRx) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  repeat' first
    | with_reducible exact handshakeSendWorkerPrefix_erases _
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem runFlushedClearWorkPrefix_erases (pid : PeerId) :
    ErasesPrefix (runFlushedClearWorkPrefix pid) (runFlushedClearWork pid) := by
  unfold runFlushedClearWorkPrefix runFlushedClearWork runWorkerPrefix
  simp only [show (Worker.clearPeerWorker == .netRx) = false from rfl, Bool.false_eq_true, ↓reduceIte]
  repeat' first
    | with_reducible exact queuedExpiredZeroKeyMaterialPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible intro x; try dsimp only)

theorem drainHandshakeSendWqPrefix_erases (upTo : Option PeerId) :
    ErasesPrefix (drainHandshakeSendWqPrefix upTo) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWqPrefix drainHandshakeSendWq
  repeat' first
    | with_reducible exact runFlushedSendWorkPrefix_erases _
    | with_reducible exact runFlushedClearWorkPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_range
    | with_reducible apply erasesPrefix_bind
    | with_reducible apply erasesPrefix_ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)
  all_goals simp_all
  all_goals subst_vars
  all_goals
    repeat' first
      | with_reducible exact runFlushedSendWorkPrefix_erases _
      | with_reducible exact runFlushedClearWorkPrefix_erases _
      | with_reducible exact erasesPrefix_lift _
      | with_reducible exact erasesPrefix_pure _
      | with_reducible apply erasesPrefix_bind
      | (with_reducible intro x; try dsimp only)

theorem timersStopPrefix_erases (pid : PeerId) :
    ErasesPrefix (timersStopPrefix pid) (timersStop pid) := by
  unfold timersStopPrefix timersStop
  repeat' first
    | with_reducible exact delTimerPrefix_erases _ _
    | with_reducible exact drainHandshakeSendWqPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem peerRemoveAfterDeadPrefix_erases (pid : PeerId) :
    ErasesPrefix (peerRemoveAfterDeadPrefix pid) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDeadPrefix peerRemoveAfterDead
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact keypairsClearPrefix_erases _
    | with_reducible exact timersStopPrefix_erases _
    | with_reducible exact drainHandshakeSendWqPrefix_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem peerRemovePrefix_erases (peer : Option PeerId) :
    ErasesPrefix (peerRemovePrefix peer) (peerRemove peer) := by
  unfold peerRemovePrefix peerRemove
  cases peer <;> simp only
  all_goals
    repeat' first
      | with_reducible exact peerMakeDeadPrefix_erases _
      | with_reducible exact peerRemoveAfterDeadPrefix_erases _
      | with_reducible exact erasesPrefix_lift _
      | with_reducible exact erasesPrefix_pure _
      | with_reducible apply erasesPrefix_bind
      | (with_reducible split)
      | (with_reducible intro x; try dsimp only)

theorem peerRemoveAllPrefix_erases : ErasesPrefix peerRemoveAllPrefix peerRemoveAll := by
  unfold peerRemoveAllPrefix peerRemoveAll
  repeat' first
    | with_reducible exact freeAllowedIpsPrefix_erases
    | with_reducible exact peerMakeDeadPrefix_erases _
    | with_reducible exact peerRemoveAfterDeadPrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_forIn
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

/-- Independent lower-call and scalar bookkeeping contracts. They impose no
queue progress, pending-work consistency or saved-reference credit condition. -/
structure PeerRemovalContracts (I : List LifetimeEvent → World → Prop) : Prop where
  socket : SocketContracts I
  indexInsert : ∀ pid kind, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (WG.indexInsert pid kind))
  indexRemove : ∀ pid kind, PrefixPreserves I LifetimeEvent.Safe (liftPrefix (WG.indexRemove pid kind))
  keypairPut : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (keypairPutPrefix kp now)
  allowedIps : AllowedIpsContracts I
  sendErase : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue.erase pid}))
  clearErase : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue.erase pid}))
  decrement : PrefixPreserves I LifetimeEvent.Safe
    (liftPrefix (modifyDev fun d => {d with numPeers := d.numPeers - 1}))

theorem allocationPeerRemoval : PeerRemovalContracts AllocationInv := by
  refine ⟨allocationSocket, indexInsert_allocation, indexRemove_allocation,
    keypairPutPrefix_allocation, allocationAllowedIps, ?_, ?_, ?_⟩
  all_goals
    try intro pid
    apply PrefixEnsures.preserves
    apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
    intro h w x v hi hr
    apply hi.congr
    · cases hr
      unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [Option.bind_map, Function.comp_def]
    · cases hr
      simp [allocationMetadata, deviceAllocationMetadata, Option.map_map, Function.comp_def] <;> rfl

theorem runFlushedSendWorkPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (runFlushedSendWorkPrefix pid) := by
  unfold runFlushedSendWorkPrefix
  apply PrefixPreserves.bind (r.sendErase pid)
  intro _
  apply AmbientContracts.drop (Q := fun _ _ => True)
  apply PrefixEnsures.bind (c.getPeer (fun _ => True) pid)
  intro p
  have ht : AmbientSpec I (fun v => True ∧ v.1.slots pid = some p.internalId)
      (do setPeerMixed pid {p with handshakePending := false}
          runWorkerPrefix .sendWorker (handshakeSendWorkerPrefix pid)) (fun _ _ => True) := by
    apply PrefixEnsures.bind (c.setPeer (fun _ => True) pid {p with handshakePending := false})
    intro _
    exact PrefixEnsures.consequence
      (runWorkerPrefix_preserves c.safe c.kernelStable .sendWorker
        (handshakeSendWorkerPrefix_preserves c r.socket r.indexInsert pid))
      (fun _ _ hi => hi.1) (fun _ _ _ hi => ⟨hi, True.intro⟩)
  dsimp only
  split
  · exact PrefixEnsures.bind (c.invariant (α := Unit)
      (fun v => True ∧ v.1.slots pid = some p.internalId)
      "queued work without a pending flag") (fun _ => ht)
  · exact ht

theorem runFlushedClearWorkPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (runFlushedClearWorkPrefix pid) :=
  PrefixPreserves.bind (r.clearErase pid) (fun _ =>
    runWorkerPrefix_preserves c.safe c.kernelStable .clearPeerWorker
      (queuedExpiredZeroKeyMaterialPrefix_preserves c r.indexRemove r.keypairPut pid))

theorem drainHandshakeSendWqPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (upTo : Option PeerId) : PrefixPreserves I LifetimeEvent.Safe (drainHandshakeSendWqPrefix upTo) := by
  unfold drainHandshakeSendWqPrefix
  repeat' first
    | with_reducible exact runFlushedSendWorkPrefix_preserves c r _
    | with_reducible exact runFlushedClearWorkPrefix_preserves c r _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (peekUnit_sameKernel _))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (resolveUnit_sameKernel _ _ _))
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr; rfl))
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr))
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.range _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | with_reducible apply PrefixPreserves.ite
    | (with_reducible intro x; try dsimp only)
    | (with_reducible split)

theorem timersStopPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (timersStopPrefix pid) := by
  unfold timersStopPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (delTimerPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact drainHandshakeSendWqPrefix_preserves c r _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem peerRemoveAfterDeadPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (peerRemoveAfterDeadPrefix pid) := by
  unfold peerRemoveAfterDeadPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact keypairsClearPrefix_preserves_ambient c r.keypairPut _
    | with_reducible exact timersStopPrefix_preserves c r _
    | with_reducible exact drainHandshakeSendWqPrefix_preserves c r _
    | with_reducible exact r.decrement
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | exact AmbientContracts.drop (c.kernel (fun _ => True) _ (by intro w x v hr; cases hr))
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem peerRemovePrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (peer : Option PeerId) : PrefixPreserves I LifetimeEvent.Safe (peerRemovePrefix peer) := by
  unfold peerRemovePrefix
  repeat' first
    | with_reducible exact peerMakeDeadPrefix_preserves c r.allowedIps _
    | with_reducible exact peerRemoveAfterDeadPrefix_preserves c r _
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.invariant (fun _ => True) _)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem peerRemoveAllPrefix_preserves (c : AmbientContracts I) (r : PeerRemovalContracts I) :
    PrefixPreserves I LifetimeEvent.Safe peerRemoveAllPrefix := by
  unfold peerRemoveAllPrefix
  repeat' first
    | with_reducible exact freeAllowedIpsPrefix_preserves c r.allowedIps.nodes
    | with_reducible exact peerMakeDeadPrefix_preserves c r.allowedIps _
    | with_reducible exact peerRemoveAfterDeadPrefix_preserves c r _
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible intro x; try dsimp only)

inductive PeerRemovalCall where
  | sendWork (pid : PeerId)
  | clearWork (pid : PeerId)
  | drain (upTo : Option PeerId)
  | stopTimers (pid : PeerId)
  | afterDead (pid : PeerId)
  | remove (peer : Option PeerId)
  | removeAll

namespace PeerRemovalCall

def original : PeerRemovalCall → M Unit
  | .sendWork pid => runFlushedSendWork pid
  | .clearWork pid => runFlushedClearWork pid
  | .drain upTo => drainHandshakeSendWq upTo
  | .stopTimers pid => timersStop pid
  | .afterDead pid => peerRemoveAfterDead pid
  | .remove peer => peerRemove peer
  | .removeAll => peerRemoveAll

def observed : PeerRemovalCall → MixedM Unit
  | .sendWork pid => runFlushedSendWorkPrefix pid
  | .clearWork pid => runFlushedClearWorkPrefix pid
  | .drain upTo => drainHandshakeSendWqPrefix upTo
  | .stopTimers pid => timersStopPrefix pid
  | .afterDead pid => peerRemoveAfterDeadPrefix pid
  | .remove peer => peerRemovePrefix peer
  | .removeAll => peerRemoveAllPrefix

theorem erases (call : PeerRemovalCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | sendWork pid => exact runFlushedSendWorkPrefix_erases pid
  | clearWork pid => exact runFlushedClearWorkPrefix_erases pid
  | drain upTo => exact drainHandshakeSendWqPrefix_erases upTo
  | stopTimers pid => exact timersStopPrefix_erases pid
  | afterDead pid => exact peerRemoveAfterDeadPrefix_erases pid
  | remove peer => exact peerRemovePrefix_erases peer
  | removeAll => exact peerRemoveAllPrefix_erases

theorem preserves_ambient (c : AmbientContracts I) (r : PeerRemovalContracts I)
    (call : PeerRemovalCall) : PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | sendWork pid => exact runFlushedSendWorkPrefix_preserves c r pid
  | clearWork pid => exact runFlushedClearWorkPrefix_preserves c r pid
  | drain upTo => exact drainHandshakeSendWqPrefix_preserves c r upTo
  | stopTimers pid => exact timersStopPrefix_preserves c r pid
  | afterDead pid => exact peerRemoveAfterDeadPrefix_preserves c r pid
  | remove peer => exact peerRemovePrefix_preserves c r peer
  | removeAll => exact peerRemoveAllPrefix_preserves c r

theorem allocation (call : PeerRemovalCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationPeerRemoval

end PeerRemovalCall
end Leanux.Proofs.WG.Lifetimes
