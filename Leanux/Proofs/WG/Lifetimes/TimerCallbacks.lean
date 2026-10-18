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
  if ← liftWGPrefix (branchCmp .retransmitGiveUp (attempts > MAX_TIMER_HANDSHAKES) attempts MAX_TIMER_HANDSHAKES) then
    delTimerPrefix pid .sendKeepalive
    purgeStagedPacketsPrefix pid
    if ← liftWGPrefix (branch .retransmitZeroKeyNotPending !((← getPeerMixed pid).timerPending .zeroKeyMaterial)) then
      discard <| modPeerTimerPrefix .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
  else
    modifyPeerKeysPrefix pid fun p => {p with timerHandshakeAttempts := p.timerHandshakeAttempts + 1}
    clearPeerEndpointSrcPrefix pid
    sendQueuedHandshakeInitiationPrefix pid true

def expiredSendKeepalivePrefix (pid : PeerId) : MixedM Unit := do
  sendKeepalivePrefix pid
  if ← liftWGPrefix (branch .keepaliveNeedAnother (← getPeerMixed pid).timerNeedAnotherKeepalive) then
    modifyPeerKeysPrefix pid fun p => {p with timerNeedAnotherKeepalive := false}
    discard <| modPeerTimerPrefix .timerJiffiesExpiredKeepalive pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS

def expiredNewHandshakePrefix (pid : PeerId) : MixedM Unit := do
  clearPeerEndpointSrcPrefix pid
  sendQueuedHandshakeInitiationPrefix pid false

def expiredZeroKeyMaterialPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftWGPrefix (branch .zeroKeyAlive !(← getPeerMixed pid).isDead) then
    peerGetMixed pid
    if ← liftWGPrefix (branch .zeroKeyAlreadyQueued ((← liftWGPrefix getDev).clearWorkQueue.contains pid && !(← liftWGPrefix (peekQueuedUnit .clearPeerWorker pid)))) then
      peerPutMixed (some pid)
    else
      liftWGPrefix (recordQueued .clearPeerWorker pid)
      liftWGPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]})

def expiredSendPersistentKeepalivePrefix (pid : PeerId) : MixedM Unit := do
  if ← liftWGPrefix (branch .persistentKeepaliveInterval ((← getPeerMixed pid).persistentKeepaliveInterval != 0)) then
    sendKeepalivePrefix pid

def timerCallbackPrefix (pid : PeerId) : PeerTimer → MixedM Unit
  | .retransmitHandshake => expiredRetransmitHandshakePrefix pid
  | .sendKeepalive => expiredSendKeepalivePrefix pid
  | .newHandshake => expiredNewHandshakePrefix pid
  | .zeroKeyMaterial => expiredZeroKeyMaterialPrefix pid
  | .persistentKeepalive => expiredSendPersistentKeepalivePrefix pid

theorem expiredRetransmitHandshakePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (expiredRetransmitHandshakePrefix pid) (expiredRetransmitHandshake pid) := by
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
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredSendKeepalivePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (expiredSendKeepalivePrefix pid) (expiredSendKeepalive pid) := by
  unfold expiredSendKeepalivePrefix expiredSendKeepalive modifyPeerKeysPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind, bind_assoc]
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact setPeerMixed_erases _ _
    | with_reducible exact sendKeepalivePrefix_erases _
    | with_reducible exact modPeerTimerPrefix_erases _ _ _ _
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredNewHandshakePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (expiredNewHandshakePrefix pid) (expiredNewHandshake pid) :=
  erasesStatePrefix_bind (clearPeerEndpointSrcPrefix_erases pid) (fun _ => sendQueuedHandshakeInitiationPrefix_erases pid false)

theorem expiredZeroKeyMaterialPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (expiredZeroKeyMaterialPrefix pid) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterialPrefix expiredZeroKeyMaterial
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact peerGetMixed_erases _
    | with_reducible exact peerPutMixed_erases _
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredSendPersistentKeepalivePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (expiredSendPersistentKeepalivePrefix pid) (expiredSendPersistentKeepalive pid) := by
  unfold expiredSendPersistentKeepalivePrefix expiredSendPersistentKeepalive
  repeat' first
    | with_reducible exact getPeerMixed_erases _
    | with_reducible exact sendKeepalivePrefix_erases _
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | with_reducible exact erasesStatePrefix_pure _
    | with_reducible apply erasesStatePrefix_bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem timerCallbackPrefix_erases (pid : PeerId) (timer : PeerTimer) :
    ErasesStatePrefix (timerCallbackPrefix pid timer) (timerCallback pid timer) := by
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshakePrefix_erases pid
  | sendKeepalive => exact expiredSendKeepalivePrefix_erases pid
  | newHandshake => exact expiredNewHandshakePrefix_erases pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterialPrefix_erases pid
  | persistentKeepalive => exact expiredSendPersistentKeepalivePrefix_erases pid

/-- Scalar queue mutations have independent ambient obligations. Concrete
allocation geometry discharges both, without a reference-credit invariant. -/
structure TimerQueueContracts (I : List LifetimeEvent → WGWorld → Prop) : Prop where
  send : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))
  clear : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
    (liftWGPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}))

theorem expiredRetransmitHandshakePrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (q : TimerQueueContracts I) (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (expiredRetransmitHandshakePrefix pid) := by
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
    | with_reducible exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredSendKeepalivePrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (expiredSendKeepalivePrefix pid) := by
  unfold expiredSendKeepalivePrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | with_reducible exact sendKeepalivePrefix_preserves_ambient c t _
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact AmbientContracts.drop (modPeerTimerPrefix_spec c (fun _ => True) _ _ _ _)
    | with_reducible exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl))
    | with_reducible exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredNewHandshakePrefix_preserves (c : AmbientContracts I) (q : TimerQueueContracts I)
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (expiredNewHandshakePrefix pid) :=
  StatePrefixEnsures.bind (AmbientContracts.drop (clearPeerEndpointSrcPrefix_spec c (fun _ => True) pid))
    (fun _ => sendQueuedHandshakeInitiationPrefix_preserves_ambient c q.send pid false)

theorem expiredZeroKeyMaterialPrefix_preserves (c : AmbientContracts I) (q : TimerQueueContracts I)
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (expiredZeroKeyMaterialPrefix pid) := by
  unfold expiredZeroKeyMaterialPrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact c.peerGet _
    | with_reducible exact c.peerPut _
    | with_reducible exact AmbientContracts.drop (c.store (fun _ => True) _ getDev_sameWGStore)
    | (maintenance_lift_action_head recordQueued; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.recordQueued .clearPeerWorker pid) (fun w => wgStoreView w = initial))))
    | (maintenance_lift_action_head peekQueuedUnit; exact AmbientContracts.drop (c.store (fun _ => True) _ (fun initial => hoare_liftAmbient (AmbientM.peekQueuedUnit .clearPeerWorker pid) (fun w => wgStoreView w = initial))))
    | with_reducible exact q.clear _
    | with_reducible exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem expiredSendPersistentKeepalivePrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (expiredSendPersistentKeepalivePrefix pid) := by
  unfold expiredSendPersistentKeepalivePrefix
  repeat' first
    | with_reducible exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _)
    | with_reducible exact AmbientContracts.drop (c.branch (fun _ => True) _ _)
    | with_reducible exact sendKeepalivePrefix_preserves_ambient c t _
    | with_reducible exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi)
    | with_reducible apply StatePrefixEnsures.bind
    | (with_reducible split)
    | (with_reducible intro x; try dsimp only)

theorem timerCallbackPrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (q : TimerQueueContracts I) (pid : PeerId) (timer : PeerTimer) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (timerCallbackPrefix pid timer) := by
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshakePrefix_preserves c t q pid
  | sendKeepalive => exact expiredSendKeepalivePrefix_preserves c t pid
  | newHandshake => exact expiredNewHandshakePrefix_preserves c q pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterialPrefix_preserves c q pid
  | persistentKeepalive => exact expiredSendPersistentKeepalivePrefix_preserves c t pid

theorem clearWorkQueue_identity_metadata (pid : PeerId) :
    SameView (fun w => (identityView w, allocationMetadata w))
      (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]}) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x v ambient' hr
  cases hr
  unfold identityView Peers.snapshot keypairResidents packetResidents allocationMetadata
  simp [Option.bind_map, Function.comp_def, deviceAllocationMetadata]
  rfl

theorem clearWorkQueue_allocation (pid : PeerId) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]})) := by
  apply StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  have hf := (ProjectedAction.iff_run_ambient _ _ _).mp (clearWorkQueue_identity_metadata pid) w ambient x v ambient' hr
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

def original : TimerCallbackCall → WG.M Unit
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

theorem erases (call : TimerCallbackCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | retransmit pid => exact expiredRetransmitHandshakePrefix_erases pid
  | keepalive pid => exact expiredSendKeepalivePrefix_erases pid
  | handshake pid => exact expiredNewHandshakePrefix_erases pid
  | zero pid => exact expiredZeroKeyMaterialPrefix_erases pid
  | persistent pid => exact expiredSendPersistentKeepalivePrefix_erases pid
  | dispatch pid timer => exact timerCallbackPrefix_erases pid timer

theorem preserves_ambient (c : AmbientContracts I) (t : TxContracts I) (q : TimerQueueContracts I)
    (call : TimerCallbackCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | retransmit pid => exact expiredRetransmitHandshakePrefix_preserves c t q pid
  | keepalive pid => exact expiredSendKeepalivePrefix_preserves c t pid
  | handshake pid => exact expiredNewHandshakePrefix_preserves c q pid
  | zero pid => exact expiredZeroKeyMaterialPrefix_preserves c q pid
  | persistent pid => exact expiredSendPersistentKeepalivePrefix_preserves c t pid
  | dispatch pid timer => exact timerCallbackPrefix_preserves c t q pid timer

theorem allocation (call : TimerCallbackCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed :=
  call.preserves_ambient allocationAmbient allocationTx allocationTimerQueue

end TimerCallbackCall

/-- Preserve the original arbitrary product-history invariant domain. -/
structure ProductTimerQueueContracts (I : List LifetimeEvent → World → Prop) : Prop where
  send : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
  clear : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
    (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with clearWorkQueue := d.clearWorkQueue ++ [pid]})))

theorem expiredRetransmitHandshakePrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (q : ProductTimerQueueContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (expiredRetransmitHandshakePrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) : PrefixEnsures I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (MonadLift.monadLift a : WG.M α))) (fun _ => I) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient a (fun w => wgStoreView w = initial)))
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold expiredRetransmitHandshakePrefix
  try simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head delTimerPrefix; exact ProductAmbientContracts.drop (delTimerPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head modPeerTimerPrefix; exact ProductAmbientContracts.drop (modPeerTimerPrefix_spec_product c (fun _ => True) _ _ _ _))
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head purgeStagedPacketsPrefix; exact purgeStagedPacketsPrefix_preserves_product c t _)
    | (maintenance_head sendKeepalivePrefix; exact sendKeepalivePrefix_preserves_product c t _)
    | (maintenance_head sendQueuedHandshakeInitiationPrefix; exact sendQueuedHandshakeInitiationPrefix_preserves_product c q.send _ _)
    | (maintenance_lift_action_head modifyDev; exact q.clear _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head branchCmp; exact ambient (AmbientM.branchCmp _ _ _ _))
    | (maintenance_lift_action_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
    | (maintenance_lift_action_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem expiredSendKeepalivePrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (expiredSendKeepalivePrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) : PrefixEnsures I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (MonadLift.monadLift a : WG.M α))) (fun _ => I) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient a (fun w => wgStoreView w = initial)))
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold expiredSendKeepalivePrefix
  try simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head delTimerPrefix; exact ProductAmbientContracts.drop (delTimerPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head modPeerTimerPrefix; exact ProductAmbientContracts.drop (modPeerTimerPrefix_spec_product c (fun _ => True) _ _ _ _))
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head purgeStagedPacketsPrefix; exact purgeStagedPacketsPrefix_preserves_product c t _)
    | (maintenance_head sendKeepalivePrefix; exact sendKeepalivePrefix_preserves_product c t _)
    | (maintenance_head sendQueuedHandshakeInitiationPrefix; exact sendQueuedHandshakeInitiationPrefix_preserves_product c q.send _ _)
    | (maintenance_lift_action_head modifyDev; exact q.clear _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head branchCmp; exact ambient (AmbientM.branchCmp _ _ _ _))
    | (maintenance_lift_action_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
    | (maintenance_lift_action_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem expiredNewHandshakePrefix_preserves_product (c : ProductAmbientContracts I) (q : ProductTimerQueueContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (expiredNewHandshakePrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) : PrefixEnsures I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (MonadLift.monadLift a : WG.M α))) (fun _ => I) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient a (fun w => wgStoreView w = initial)))
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold expiredNewHandshakePrefix
  try simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head delTimerPrefix; exact ProductAmbientContracts.drop (delTimerPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head modPeerTimerPrefix; exact ProductAmbientContracts.drop (modPeerTimerPrefix_spec_product c (fun _ => True) _ _ _ _))
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head purgeStagedPacketsPrefix; exact purgeStagedPacketsPrefix_preserves_product c t _)
    | (maintenance_head sendKeepalivePrefix; exact sendKeepalivePrefix_preserves_product c t _)
    | (maintenance_head sendQueuedHandshakeInitiationPrefix; exact sendQueuedHandshakeInitiationPrefix_preserves_product c q.send _ _)
    | (maintenance_lift_action_head modifyDev; exact q.clear _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head branchCmp; exact ambient (AmbientM.branchCmp _ _ _ _))
    | (maintenance_lift_action_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
    | (maintenance_lift_action_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem expiredZeroKeyMaterialPrefix_preserves_product (c : ProductAmbientContracts I) (q : ProductTimerQueueContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (expiredZeroKeyMaterialPrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) : PrefixEnsures I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (MonadLift.monadLift a : WG.M α))) (fun _ => I) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient a (fun w => wgStoreView w = initial)))
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold expiredZeroKeyMaterialPrefix
  try simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head delTimerPrefix; exact ProductAmbientContracts.drop (delTimerPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head modPeerTimerPrefix; exact ProductAmbientContracts.drop (modPeerTimerPrefix_spec_product c (fun _ => True) _ _ _ _))
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head purgeStagedPacketsPrefix; exact purgeStagedPacketsPrefix_preserves_product c t _)
    | (maintenance_head sendKeepalivePrefix; exact sendKeepalivePrefix_preserves_product c t _)
    | (maintenance_head sendQueuedHandshakeInitiationPrefix; exact sendQueuedHandshakeInitiationPrefix_preserves_product c q.send _ _)
    | (maintenance_lift_action_head modifyDev; exact q.clear _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head branchCmp; exact ambient (AmbientM.branchCmp _ _ _ _))
    | (maintenance_lift_action_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
    | (maintenance_lift_action_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem expiredSendPersistentKeepalivePrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I) (pid : PeerId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (expiredSendPersistentKeepalivePrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) : PrefixEnsures I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (MonadLift.monadLift a : WG.M α))) (fun _ => I) :=
    ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _
      (fun initial => hoare_liftAmbient a (fun w => wgStoreView w = initial)))
  change PrefixEnsures I LifetimeEvent.Safe _ (fun _ => I)
  unfold expiredSendPersistentKeepalivePrefix
  try simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head peerGetMixed; exact c.peerGet _)
    | (maintenance_head peerPutMixed; exact c.peerPut _)
    | (maintenance_head delTimerPrefix; exact ProductAmbientContracts.drop (delTimerPrefix_spec_product c (fun _ => True) _ _))
    | (maintenance_head modPeerTimerPrefix; exact ProductAmbientContracts.drop (modPeerTimerPrefix_spec_product c (fun _ => True) _ _ _ _))
    | (maintenance_head clearPeerEndpointSrcPrefix; exact ProductAmbientContracts.drop (clearPeerEndpointSrcPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head purgeStagedPacketsPrefix; exact purgeStagedPacketsPrefix_preserves_product c t _)
    | (maintenance_head sendKeepalivePrefix; exact sendKeepalivePrefix_preserves_product c t _)
    | (maintenance_head sendQueuedHandshakeInitiationPrefix; exact sendQueuedHandshakeInitiationPrefix_preserves_product c q.send _ _)
    | (maintenance_lift_action_head modifyDev; exact q.clear _)
    | (maintenance_lift_action_head getDev; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ getDev_sameWGStore))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head branchCmp; exact ambient (AmbientM.branchCmp _ _ _ _))
    | (maintenance_lift_action_head recordQueued; exact ambient (AmbientM.recordQueued _ _))
    | (maintenance_lift_action_head peekQueuedUnit; exact ambient (AmbientM.peekQueuedUnit _ _))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem timerCallbackPrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (q : ProductTimerQueueContracts I) (pid : PeerId) (timer : PeerTimer) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (timerCallbackPrefix pid timer)) := by
  cases timer with
  | retransmitHandshake => exact expiredRetransmitHandshakePrefix_preserves_product c t q pid
  | sendKeepalive => exact expiredSendKeepalivePrefix_preserves_product c t pid
  | newHandshake => exact expiredNewHandshakePrefix_preserves_product c q pid
  | zeroKeyMaterial => exact expiredZeroKeyMaterialPrefix_preserves_product c q pid
  | persistentKeepalive => exact expiredSendPersistentKeepalivePrefix_preserves_product c t pid

namespace TimerCallbackCall

theorem preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (q : ProductTimerQueueContracts I) (call : TimerCallbackCall) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | retransmit pid => exact expiredRetransmitHandshakePrefix_preserves_product c t q pid
  | keepalive pid => exact expiredSendKeepalivePrefix_preserves_product c t pid
  | handshake pid => exact expiredNewHandshakePrefix_preserves_product c q pid
  | zero pid => exact expiredZeroKeyMaterialPrefix_preserves_product c q pid
  | persistent pid => exact expiredSendPersistentKeepalivePrefix_preserves_product c t pid
  | dispatch pid timer => exact timerCallbackPrefix_preserves_product c t q pid timer

end TimerCallbackCall

end Leanux.Proofs.WG.Lifetimes
