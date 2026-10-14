import Leanux.Proofs.WG.Lifetimes.KeyMaintenance
import Leanux.Proofs.WG.Lifetimes.SocketCache
import Leanux.Proofs.WG.Lifetimes.TxStagingCalls
import Leanux.WG.Timers

/-! Complete original timer callbacks. Each resolved object access is observed
in source order, including the fresh getter before a keepalive reset and the
acquire/put pair when clear work is already queued. Timer detachment is an
outer environment action, not a premise or effect asserted here. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing

def expiredRetransmitHandshakePrefix (pid : PeerId) : MixedM Unit := do
  let attempts := (← getPeerMixed pid).timerHandshakeAttempts
  if ← liftPrefix (branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES) then
    delTimerPrefix pid .sendKeepalive
    purgeStagedPacketsPrefix pid
    if ← liftPrefix (branch .retransmitZeroKeyNotPending !((← getPeerMixed pid).timerPending .zeroKeyMaterial)) then
      discard <| modPeerTimerPrefix .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
  else
    modifyPeerKeysPrefix pid fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1}
    clearPeerEndpointSrcPrefix pid
    sendQueuedHandshakeInitiationPrefix pid true

def expiredSendKeepalivePrefix (pid : PeerId) : MixedM Unit := do
  sendKeepalivePrefix pid
  if ← liftPrefix (branch .keepaliveNeedAnother (← getPeerMixed pid).timerNeedAnotherKeepalive) then
    modifyPeerKeysPrefix pid fun p => {p with timerNeedAnotherKeepalive := false}
    discard <| modPeerTimerPrefix .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS

def expiredNewHandshakePrefix (pid : PeerId) : MixedM Unit := do
  clearPeerEndpointSrcPrefix pid
  sendQueuedHandshakeInitiationPrefix pid false

def expiredZeroKeyMaterialPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftPrefix (branch .zeroKeyAlive !(← getPeerMixed pid).isDead) then
    peerGetMixed pid
    if ← liftPrefix (branch .zeroKeyAlreadyQueued ((← liftPrefix getDev).clearWorkQueue.contains pid)) then
      peerPutMixed (some pid)
    else
      liftPrefix (recordQueued .clearPeerWorker pid)
      liftPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]})

def expiredSendPersistentKeepalivePrefix (pid : PeerId) : MixedM Unit := do
  if ← liftPrefix (branch .persistentKeepaliveInterval ((← getPeerMixed pid).persistentKeepaliveInterval != 0)) then
    sendKeepalivePrefix pid

def timerCallbackPrefix (pid : PeerId) : PeerTimer → MixedM Unit
  | .retransmitHandshake => expiredRetransmitHandshakePrefix pid
  | .sendKeepalive => expiredSendKeepalivePrefix pid
  | .newHandshake => expiredNewHandshakePrefix pid
  | .zeroKeyMaterial => expiredZeroKeyMaterialPrefix pid
  | .persistentKeepalive => expiredSendPersistentKeepalivePrefix pid

theorem expiredRetransmitHandshakePrefix_erases (pid : PeerId) :
    ErasesPrefix (expiredRetransmitHandshakePrefix pid) (expiredRetransmitHandshake pid) := by
  unfold expiredRetransmitHandshakePrefix expiredRetransmitHandshake modifyPeerKeysPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact delTimerPrefix_erases _ _
    | with_reducible exact purgeStagedPacketsPrefix_erases _
    | with_reducible exact modPeerTimerPrefix_erases _ _ _ _
    | with_reducible exact clearPeerEndpointSrcPrefix_erases _
    | with_reducible exact sendQueuedHandshakeInitiationPrefix_erases _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredSendKeepalivePrefix_erases (pid : PeerId) :
    ErasesPrefix (expiredSendKeepalivePrefix pid) (expiredSendKeepalive pid) := by
  unfold expiredSendKeepalivePrefix expiredSendKeepalive modifyPeerKeysPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact sendKeepalivePrefix_erases _
    | with_reducible exact modPeerTimerPrefix_erases _ _ _ _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredNewHandshakePrefix_erases (pid : PeerId) :
    ErasesPrefix (expiredNewHandshakePrefix pid) (expiredNewHandshake pid) :=
  erasesPrefix_bind (clearPeerEndpointSrcPrefix_erases pid) (fun _ => sendQueuedHandshakeInitiationPrefix_erases pid false)

theorem expiredZeroKeyMaterialPrefix_erases (pid : PeerId) :
    ErasesPrefix (expiredZeroKeyMaterialPrefix pid) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterialPrefix expiredZeroKeyMaterial
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerPutMixed_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredSendPersistentKeepalivePrefix_erases (pid : PeerId) :
    ErasesPrefix (expiredSendPersistentKeepalivePrefix pid) (expiredSendPersistentKeepalive pid) := by
  unfold expiredSendPersistentKeepalivePrefix expiredSendPersistentKeepalive
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact sendKeepalivePrefix_erases _
    | with_reducible exact erasesPrefix_lift _
    | with_reducible exact erasesPrefix_pure _
    | with_reducible apply erasesPrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem timerCallbackPrefix_erases (pid : PeerId) (timer : PeerTimer) :
    ErasesPrefix (timerCallbackPrefix pid timer) (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshakePrefix_erases pid
  | sendKeepalive => exact expiredSendKeepalivePrefix_erases pid
  | newHandshake => exact expiredNewHandshakePrefix_erases pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterialPrefix_erases pid
  | persistentKeepalive => exact expiredSendPersistentKeepalivePrefix_erases pid

/-- Scalar queue mutations have independent ambient obligations. Concrete
allocation geometry discharges both, without a reference-credit invariant. -/
structure TimerQueueContracts (I : List LifetimeEvent → World → Prop) : Prop where
  send : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))
  clear : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}))

theorem expiredRetransmitHandshakePrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (q : TimerQueueContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (expiredRetransmitHandshakePrefix pid) := by
  unfold expiredRetransmitHandshakePrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (c.branchCmp (fun _ => True) _ _ _ _)
    | with_reducible exact AmbientContracts.drop (delTimerPrefix_spec c (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (modPeerTimerPrefix_spec c (fun _ => True) _ _ _ _)
    | with_reducible exact AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact purgeStagedPacketsPrefix_preserves_ambient c t _
    | with_reducible exact sendQueuedHandshakeInitiationPrefix_preserves_ambient c q.send _ _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredSendKeepalivePrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (expiredSendKeepalivePrefix pid) := by
  unfold expiredSendKeepalivePrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | with_reducible exact sendKeepalivePrefix_preserves_ambient c t _
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (modPeerTimerPrefix_spec c (fun _ => True) _ _ _ _)
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredNewHandshakePrefix_preserves (c : AmbientContracts I) (q : TimerQueueContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (expiredNewHandshakePrefix pid) :=
  PrefixPreserves.bind (AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) pid))
    (fun _ => sendQueuedHandshakeInitiationPrefix_preserves_ambient c q.send pid false)

theorem expiredZeroKeyMaterialPrefix_preserves (c : AmbientContracts I) (q : TimerQueueContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (expiredZeroKeyMaterialPrefix pid) := by
  unfold expiredZeroKeyMaterialPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ getDev_sameKernel)
    | with_reducible exact AmbientContracts.drop (c.kernel (fun _ => True) _ (recordQueued_sameKernel _ _))
    | with_reducible exact q.clear _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredSendPersistentKeepalivePrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (expiredSendPersistentKeepalivePrefix pid) := by
  unfold expiredSendPersistentKeepalivePrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact sendKeepalivePrefix_preserves_ambient c t _
    | with_reducible exact PrefixPreserves.pure c.safe _
    | with_reducible apply PrefixPreserves.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem timerCallbackPrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (q : TimerQueueContracts I) (pid : PeerId) (timer : PeerTimer) :
    PrefixPreserves I LifetimeEvent.Safe (timerCallbackPrefix pid timer) := by
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshakePrefix_preserves c t q pid
  | sendKeepalive => exact expiredSendKeepalivePrefix_preserves c t pid
  | newHandshake => exact expiredNewHandshakePrefix_preserves c q pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterialPrefix_preserves c q pid
  | persistentKeepalive => exact expiredSendPersistentKeepalivePrefix_preserves c t pid

theorem clearWorkQueue_identity_metadata (pid : PeerId) :
    SameView (fun w => (identityView w, allocationMetadata w))
      (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}) := by
  intro w x v hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata
  simp [Option.bind_map, Function.comp_def, deviceAllocationMetadata]
  rfl

theorem clearWorkQueue_allocation (pid : PeerId) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe
      (liftPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]})) := by
  apply PrefixEnsures.preserves
  apply PrefixEnsures.lift _ (fun _ _ hi => hi.safe)
  intro h w x v hi hr
  have hf := clearWorkQueue_identity_metadata pid w x v hr
  exact hi.congr (congrArg Prod.fst hf) (congrArg Prod.snd hf)

theorem allocationTimerQueue : TimerQueueContracts AllocationInv :=
  ⟨sendWorkQueue_allocation, clearWorkQueue_allocation⟩

inductive TimerCallbackCall where
  | retransmit (pid : PeerId)
  | keepalive (pid : PeerId)
  | handshake (pid : PeerId)
  | zero (pid : PeerId)
  | persistent (pid : PeerId)
  | dispatch (pid : PeerId) (timer : PeerTimer)

namespace TimerCallbackCall

def original : TimerCallbackCall → M Unit
  | .retransmit pid => expiredRetransmitHandshake pid
  | .keepalive pid => expiredSendKeepalive pid
  | .handshake pid => expiredNewHandshake pid
  | .zero pid => expiredZeroKeyMaterial pid
  | .persistent pid => expiredSendPersistentKeepalive pid
  | .dispatch pid timer => timerCallback pid timer

def observed : TimerCallbackCall → MixedM Unit
  | .retransmit pid => expiredRetransmitHandshakePrefix pid
  | .keepalive pid => expiredSendKeepalivePrefix pid
  | .handshake pid => expiredNewHandshakePrefix pid
  | .zero pid => expiredZeroKeyMaterialPrefix pid
  | .persistent pid => expiredSendPersistentKeepalivePrefix pid
  | .dispatch pid timer => timerCallbackPrefix pid timer

theorem erases (call : TimerCallbackCall) : ErasesPrefix call.observed call.original := by
  cases call with
  | retransmit pid => exact expiredRetransmitHandshakePrefix_erases pid
  | keepalive pid => exact expiredSendKeepalivePrefix_erases pid
  | handshake pid => exact expiredNewHandshakePrefix_erases pid
  | zero pid => exact expiredZeroKeyMaterialPrefix_erases pid
  | persistent pid => exact expiredSendPersistentKeepalivePrefix_erases pid
  | dispatch pid timer => exact timerCallbackPrefix_erases pid timer

theorem preserves_ambient (c : AmbientContracts I) (t : TxContracts I) (q : TimerQueueContracts I)
    (call : TimerCallbackCall) : PrefixPreserves I LifetimeEvent.Safe call.observed := by
  cases call with
  | retransmit pid => exact expiredRetransmitHandshakePrefix_preserves c t q pid
  | keepalive pid => exact expiredSendKeepalivePrefix_preserves c t pid
  | handshake pid => exact expiredNewHandshakePrefix_preserves c q pid
  | zero pid => exact expiredZeroKeyMaterialPrefix_preserves c q pid
  | persistent pid => exact expiredSendPersistentKeepalivePrefix_preserves c t pid
  | dispatch pid timer => exact timerCallbackPrefix_preserves c t q pid timer

theorem allocation (call : TimerCallbackCall) :
    PrefixPreserves AllocationInv LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationTx allocationTimerQueue

end TimerCallbackCall
end Leanux.Proofs.WG.Lifetimes
