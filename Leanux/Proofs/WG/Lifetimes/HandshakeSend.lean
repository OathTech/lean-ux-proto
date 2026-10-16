import Leanux.Proofs.WG.Lifetimes.HandshakeCalls
import Leanux.Proofs.WG.Lifetimes.TxCompletion
import Leanux.Proofs.WG.Lifetimes.Session

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Complete original handshake send calls. Allocation refusal and ordinary
negative socket returns are normal returns; Stops retain their access prefix
and skip later timer work or the worker's final put. No scheduler or saved
reference ownership assertion is added. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

/-- The original buffer helper is an allocation check followed by the original
socket send, with its Boolean return discarded. This equality has no premise. -/
theorem sendBufferToPeer_eq (pid : PeerId) (bytes : List UInt8) :
    sendBufferToPeer pid bytes = (do
      if ← branch .sendBufNoMem !(← hiddenAlloc .sendBufSkb) then return
      discard <| sendSkbToPeer pid bytes HANDSHAKE_DSCP) := by
  have bind_if {α β : Type} (p : Prop) [Decidable p] (a b : WG.M α) (f : α → WG.M β) :
      ((if p then a else b) >>= f) = (if p then a >>= f else b >>= f) := by
    split <;> rfl
  simp only [sendBufferToPeer, sendSkbToPeer, Functor.discard, map_const,
    Function.comp_apply, Function.const, map_eq_pure_bind, bind_assoc, pure_bind,
    bind_if, bind_pure_unit]

def sendBufferToPeerPrefix (pid : PeerId) (bytes : List UInt8) : MixedM Unit := do
  if ← liftWGPrefix (branch .sendBufNoMem !(← liftWGPrefix (hiddenAlloc .sendBufSkb))) then return
  discard <| sendSkbToPeerPrefix pid bytes HANDSHAKE_DSCP

def timersSessionDerivedPrefix (pid : PeerId) : MixedM Unit :=
  discard <| modPeerTimerPrefix .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS

def timersHandshakeInitiatedPrefix (pid : PeerId) : MixedM Unit := do
  let jc ← liftWGPrefix (callerJiffies .timerJiffiesHandshakeInitiated)
  let jitter ← liftWGPrefix (jitterBelowRekeyTimeout .retransmitJitter)
  if ← modPeerTimerGuardPrefix pid then
    armTimerPrefix pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) jc

def sendHandshakeInitiationPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftWGPrefix (branchExpired .initRateLimited (← getPeerMixed pid).lastSentHandshake REKEY_TIMEOUT (!·)) then return
  let now ← liftWGPrefix (hiddenClock64 .initLastSent)
  modifyPeerKeysPrefix pid fun p => {p with lastSentHandshake := now}
  let created ← createInitiationPrefix pid
  if ← liftWGPrefix (branch .initCreated created.isSome) then
    let some msg := created | liftWGPrefix (invariant "unreachable")
    let msg ← addMacToPacketPrefix pid msg
    timersTraversalPrefix pid
    timersAnyAuthenticatedPacketSentPrefix pid
    let now ← liftWGPrefix (hiddenClock64 .initLastSentAgain)
    modifyPeerKeysPrefix pid fun p => {p with lastSentHandshake := now}
    sendBufferToPeerPrefix pid msg
    timersHandshakeInitiatedPrefix pid

def sendHandshakeResponsePrefix (pid : PeerId) : MixedM Unit := do
  let now ← liftWGPrefix (hiddenClock64 .respLastSent)
  modifyPeerKeysPrefix pid fun p => {p with lastSentHandshake := now}
  let created ← createResponsePrefix pid
  if ← liftWGPrefix (branch .respCreated created.isSome) then
    let some msg := created | liftWGPrefix (invariant "unreachable")
    let msg ← addMacToPacketPrefix pid msg
    if ← liftWGPrefix (branch .respSessionBegun (← beginSessionPrefix pid)) then
      timersSessionDerivedPrefix pid
      timersTraversalPrefix pid
      timersAnyAuthenticatedPacketSentPrefix pid
      let now ← liftWGPrefix (hiddenClock64 .respLastSentAgain)
      modifyPeerKeysPrefix pid fun p => {p with lastSentHandshake := now}
      sendBufferToPeerPrefix pid msg

def handshakeSendWorkerPrefix (pid : PeerId) : MixedM Unit := do
  sendHandshakeInitiationPrefix pid
  peerPutMixed (some pid)

theorem sendBufferToPeerPrefix_erases (pid : PeerId) (bytes : List UInt8) :
    ErasesStatePrefix (sendBufferToPeerPrefix pid bytes) (sendBufferToPeer pid bytes) := by
  rw [sendBufferToPeer_eq]
  unfold sendBufferToPeerPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | consume_conditional
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head sendSkbToPeerPrefix; exact sendSkbToPeerPrefix_erases _ _ _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | consume_erases_modify_bind
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem timersSessionDerivedPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (timersSessionDerivedPrefix pid) (timersSessionDerived pid) := by
  exact erasesStatePrefix_bind (modPeerTimerPrefix_erases _ pid _ _) (fun _ => erasesStatePrefix_pure _)

theorem timersHandshakeInitiatedPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (timersHandshakeInitiatedPrefix pid) (timersHandshakeInitiated pid) := by
  unfold timersHandshakeInitiatedPrefix timersHandshakeInitiated
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro jc
  apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
  intro jitter
  apply erasesStatePrefix_bind (modPeerTimerGuardPrefix_erases pid)
  intro yes
  cases yes with
  | true => exact armTimerPrefix_erases _ _ _ _
  | false => exact erasesStatePrefix_pure _

theorem sendHandshakeInitiationPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (sendHandshakeInitiationPrefix pid) (sendHandshakeInitiation pid) := by
  unfold sendHandshakeInitiationPrefix sendHandshakeInitiation
  repeat' first
    | consume_conditional
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head createInitiationPrefix; exact createInitiationPrefix_erases _)
    | (maintenance_head addMacToPacketPrefix; exact addMacToPacketPrefix_erases _ _)
    | (maintenance_head timersTraversalPrefix; exact timersTraversalPrefix_erases _)
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact timersAnyAuthenticatedPacketSentPrefix_erases _)
    | (maintenance_head sendBufferToPeerPrefix; exact sendBufferToPeerPrefix_erases _ _)
    | (maintenance_head timersHandshakeInitiatedPrefix; exact timersHandshakeInitiatedPrefix_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | consume_erases_modify_bind
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem sendHandshakeResponsePrefix_erases (pid : PeerId) :
    ErasesStatePrefix (sendHandshakeResponsePrefix pid) (sendHandshakeResponse pid) := by
  unfold sendHandshakeResponsePrefix sendHandshakeResponse
  repeat' first
    | consume_conditional
    | maintenance_erases_join
    | maintenance_erases_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head createResponsePrefix; exact createResponsePrefix_erases _)
    | (maintenance_head addMacToPacketPrefix; exact addMacToPacketPrefix_erases _ _)
    | (maintenance_head beginSessionPrefix; exact beginSessionPrefix_erases _)
    | (maintenance_head timersSessionDerivedPrefix; exact timersSessionDerivedPrefix_erases _)
    | (maintenance_head timersTraversalPrefix; exact timersTraversalPrefix_erases _)
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact timersAnyAuthenticatedPacketSentPrefix_erases _)
    | (maintenance_head sendBufferToPeerPrefix; exact sendBufferToPeerPrefix_erases _ _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_erases _ _)
    | (maintenance_head liftWGPrefix; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | consume_erases_modify_bind
    | maintenance_erases_bind
    | (maintenance_head ite; split)
    | (maintenance_head dite; split)
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem handshakeSendWorkerPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (handshakeSendWorkerPrefix pid) (handshakeSendWorker pid) :=
  erasesStatePrefix_bind (sendHandshakeInitiationPrefix_erases pid) (fun _ => peerPutMixed_erases _)

theorem sendBufferToPeerPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I)
    (P : IdentityView → Prop) (pid : PeerId) (bytes : List UInt8) :
    AmbientSpec I P (sendBufferToPeerPrefix pid bytes) (fun _ => P) := by
  have ambient {α : Type} (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      AmbientSpec I P (liftWGPrefix a) (fun _ => P) :=
    c.store P a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  change StatePrefixEnsures _ _ _ _
  unfold sendBufferToPeerPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_head sendSkbToPeerPrefix; exact sendSkbToPeerPrefix_spec c sc P _ _ _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w ∧ P (identityView w)))
    | maintenance_match
    | maintenance_intro

theorem timersSessionDerivedPrefix_spec (c : AmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (timersSessionDerivedPrefix pid) (fun _ => P) := by
  change StatePrefixEnsures _ _ _ _
  exact StatePrefixEnsures.bind (modPeerTimerPrefix_spec c P _ pid _ _) (fun _ => AmbientContracts.pure c P _)

theorem timersHandshakeInitiatedPrefix_spec (c : AmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (timersHandshakeInitiatedPrefix pid) (fun _ => P) := by
  have ambient {α : Type} (a : AmbientM α) :
      AmbientSpec I P (liftWGPrefix (StateT.lift a)) (fun _ => P) :=
    c.store P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      AmbientSpec I P (liftWGPrefix a) (fun _ => P) :=
    c.store P a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  change StatePrefixEnsures _ _ _ _
  unfold timersHandshakeInitiatedPrefix

  apply StatePrefixEnsures.bind (whole _ (Framing.callerJiffies_sameWGWorld _))
  intro jc

  apply StatePrefixEnsures.bind (whole _ (Framing.jitterBelowRekeyTimeout_sameWGWorld _))
  intro jitter

  apply StatePrefixEnsures.bind (modPeerTimerGuardPrefix_spec c P pid)
  intro yes
  cases yes with
  | true => exact armTimerPrefix_spec c P _ _ _ _
  | false => exact c.pure P _

theorem sendHandshakeInitiationPrefix_preserves (c : AmbientContracts I) (sc : SocketContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexInsert owner))))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (sendHandshakeInitiationPrefix pid) := by
  have ambient {α : Type} (a : AmbientM α) :
      AmbientSpec I (fun _ => True) (liftWGPrefix (StateT.lift a)) (fun _ => (fun _ => True)) :=
    c.store (fun _ => True) (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      AmbientSpec I (fun _ => True) (liftWGPrefix a) (fun _ => (fun _ => True)) :=
    c.store (fun _ => True) a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  change StatePrefixEnsures _ _ _ _
  unfold sendHandshakeInitiationPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head createInitiationPrefix; exact createInitiationPrefix_preserves c hi _)
    | (maintenance_head addMacToPacketPrefix; exact addMacToPacketPrefix_preserves c _ _)
    | (maintenance_head timersTraversalPrefix; exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _))
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact AmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec c (fun _ => True) _))
    | (maintenance_head sendBufferToPeerPrefix; exact AmbientContracts.drop (sendBufferToPeerPrefix_spec c sc (fun _ => True) _ _))
    | (maintenance_head timersHandshakeInitiatedPrefix; exact AmbientContracts.drop (timersHandshakeInitiatedPrefix_spec c (fun _ => True) _))
    | (maintenance_lift_action_head hiddenClock64; exact AmbientContracts.drop (ambient (AmbientM.hiddenClock64 _)))
    | (maintenance_lift_action_head branchExpired; exact AmbientContracts.drop (whole _ (Framing.branchExpired_sameWGWorld _ _ _ _)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (AmbientM.branch _ _)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem sendHandshakeResponsePrefix_preserves (c : AmbientContracts I) (sc : SocketContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexInsert owner))))
    (create : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairCreatePrefix pid))
    (put : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now))
    (replace : ∀ pid kp, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp))))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (sendHandshakeResponsePrefix pid) := by
  have ambient {α : Type} (a : AmbientM α) :
      AmbientSpec I (fun _ => True) (liftWGPrefix (StateT.lift a)) (fun _ => (fun _ => True)) :=
    c.store (fun _ => True) (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      AmbientSpec I (fun _ => True) (liftWGPrefix a) (fun _ => (fun _ => True)) :=
    c.store (fun _ => True) a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  change StatePrefixEnsures _ _ _ _
  unfold sendHandshakeResponsePrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; exact AmbientContracts.drop (modifyPeerKeysPrefix_spec_ambient c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head createResponsePrefix; exact createResponsePrefix_preserves c hi _)
    | (maintenance_head addMacToPacketPrefix; exact addMacToPacketPrefix_preserves c _ _)
    | (maintenance_head timersTraversalPrefix; exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _))
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact AmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec c (fun _ => True) _))
    | (maintenance_head sendBufferToPeerPrefix; exact AmbientContracts.drop (sendBufferToPeerPrefix_spec c sc (fun _ => True) _ _))
    | (maintenance_head beginSessionPrefix; exact beginSessionPrefix_preserves_ambient c create put replace _)
    | (maintenance_head timersSessionDerivedPrefix; exact AmbientContracts.drop (timersSessionDerivedPrefix_spec c (fun _ => True) _))
    | (maintenance_lift_action_head hiddenClock64; exact AmbientContracts.drop (ambient (AmbientM.hiddenClock64 _)))
    | (maintenance_lift_action_head branchExpired; exact AmbientContracts.drop (whole _ (Framing.branchExpired_sameWGWorld _ _ _ _)))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (ambient (AmbientM.branch _ _)))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (ambient (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head Bind.bind; apply StatePrefixEnsures.bind (Q := fun _ h w _ => I h w))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem handshakeSendWorkerPrefix_preserves (c : AmbientContracts I) (sc : SocketContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexInsert owner))))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (handshakeSendWorkerPrefix pid) := by
  exact StatePrefixEnsures.bind (sendHandshakeInitiationPrefix_preserves c sc hi pid) (fun _ => c.peerPut _)

theorem sendBufferToPeerPrefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I)
    (P : IdentityView → Prop) (pid : PeerId) (bytes : List UInt8) :
    ProductAmbientSpec I P (liftWGObserver (sendBufferToPeerPrefix pid bytes)) (fun _ => P) := by
  have ambient {α : Type} (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix a)) (fun _ => P) :=
    c.nativeStore P a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  change PrefixEnsures _ _ _ _
  unfold sendBufferToPeerPrefix
  simp only [Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind]
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_lift_action_head hiddenAlloc; exact ambient (AmbientM.hiddenAlloc _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_head sendSkbToPeerPrefix; exact sendSkbToPeerPrefix_spec_product c sc P _ _ _)
    | (maintenance_head Pure.pure; exact c.pure P _)
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ h w => I h w ∧ P (identityView w.wg)))
    | maintenance_match
    | maintenance_intro

theorem timersSessionDerivedPrefix_spec_product (c : ProductAmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (timersSessionDerivedPrefix pid)) (fun _ => P) := by
  rw [show liftWGObserver (timersSessionDerivedPrefix pid) = (liftWGObserver (modPeerTimerPrefix .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS) >>= fun _ => pure ()) from by simp only [timersSessionDerivedPrefix, Functor.discard, map_const, Function.comp_apply, Function.const, map_eq_pure_bind, liftWGObserver_bind, liftWGObserver_pure]]
  exact PrefixEnsures.bind (modPeerTimerPrefix_spec_product c P _ pid _ _) (fun _ => ProductAmbientContracts.pure c P _)

theorem timersHandshakeInitiatedPrefix_spec_product (c : ProductAmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (timersHandshakeInitiatedPrefix pid)) (fun _ => P) := by
  have ambient {α : Type} (a : AmbientM α) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => P) :=
    c.nativeStore P (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      ProductAmbientSpec I P (liftWGObserver (liftWGPrefix a)) (fun _ => P) :=
    c.nativeStore P a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  change PrefixEnsures _ _ _ _
  unfold timersHandshakeInitiatedPrefix
  rw [liftWGObserver_bind]
  apply PrefixEnsures.bind (whole _ (Framing.callerJiffies_sameWGWorld _))
  intro jc
  rw [liftWGObserver_bind]
  apply PrefixEnsures.bind (whole _ (Framing.jitterBelowRekeyTimeout_sameWGWorld _))
  intro jitter
  rw [liftWGObserver_bind]
  apply PrefixEnsures.bind (modPeerTimerGuardPrefix_spec_product c P pid)
  intro yes
  cases yes with
  | true => exact armTimerPrefix_spec_product c P _ _ _ _
  | false => simpa only [Bool.false_eq_true, ↓reduceIte, liftWGObserver_pure] using c.pure P ()

theorem sendHandshakeInitiationPrefix_preserves_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner)))))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (sendHandshakeInitiationPrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) :
      ProductAmbientSpec I (fun _ => True) (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => (fun _ => True)) :=
    c.nativeStore (fun _ => True) (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      ProductAmbientSpec I (fun _ => True) (liftWGObserver (liftWGPrefix a)) (fun _ => (fun _ => True)) :=
    c.nativeStore (fun _ => True) a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  apply PrefixEnsures.preserves
  unfold sendHandshakeInitiationPrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_head getPeerMixed; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head createInitiationPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact createInitiationPrefix_preserves_product c hi _)
    | (maintenance_head addMacToPacketPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact addMacToPacketPrefix_preserves_product c _ _)
    | (maintenance_head timersTraversalPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersTraversalPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head sendBufferToPeerPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (sendBufferToPeerPrefix_spec_product c sc (fun _ => True) _ _))
    | (maintenance_head timersHandshakeInitiatedPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersHandshakeInitiatedPrefix_spec_product c (fun _ => True) _))
    | (maintenance_lift_action_head hiddenClock64; exact ProductAmbientContracts.drop (ambient (AmbientM.hiddenClock64 _)))
    | (maintenance_lift_action_head branchExpired; exact ProductAmbientContracts.drop (whole _ (Framing.branchExpired_sameWGWorld _ _ _ _)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (AmbientM.branch _ _)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem sendHandshakeResponsePrefix_preserves_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner)))))
    (create : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairCreatePrefix pid)))
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (replace : ∀ pid kp, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp)))))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (sendHandshakeResponsePrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) :
      ProductAmbientSpec I (fun _ => True) (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => (fun _ => True)) :=
    c.nativeStore (fun _ => True) (StateT.lift a) (by intro initial; exact hoare_liftAmbient a _)
  have whole {α : Type} (a : WG.M α) (ha : SameView (id : WGWorld → WGWorld) a) :
      ProductAmbientSpec I (fun _ => True) (liftWGObserver (liftWGPrefix a)) (fun _ => (fun _ => True)) :=
    c.nativeStore (fun _ => True) a (ha.of_factor wgStoreView wgStoreView (fun _ => rfl))
  apply PrefixEnsures.preserves
  unfold sendHandshakeResponsePrefix
  repeat' first
    | consume_conditional
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_reduce
    | maintenance_reduce_match
    | maintenance_product_lift
    | (maintenance_head getPeerMixed; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head modifyPeerKeysPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (modifyPeerKeysPrefix_spec_product c (fun _ => True) _ _ (fun _ => rfl)))
    | (maintenance_head createResponsePrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact createResponsePrefix_preserves_product c hi _)
    | (maintenance_head addMacToPacketPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact addMacToPacketPrefix_preserves_product c _ _)
    | (maintenance_head timersTraversalPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersTraversalPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head sendBufferToPeerPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (sendBufferToPeerPrefix_spec_product c sc (fun _ => True) _ _))
    | (maintenance_head beginSessionPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact beginSessionPrefix_preserves_product c create put replace _)
    | (maintenance_head timersSessionDerivedPrefix; change PrefixPreserves I LifetimeEvent.Safe _; exact ProductAmbientContracts.drop (timersSessionDerivedPrefix_spec_product c (fun _ => True) _))
    | (maintenance_lift_action_head hiddenClock64; exact ProductAmbientContracts.drop (ambient (AmbientM.hiddenClock64 _)))
    | (maintenance_lift_action_head branchExpired; exact ProductAmbientContracts.drop (whole _ (Framing.branchExpired_sameWGWorld _ _ _ _)))
    | (maintenance_lift_action_head branch; exact ProductAmbientContracts.drop (ambient (AmbientM.branch _ _)))
    | (maintenance_lift_action_head invariant; exact ProductAmbientContracts.drop (ambient (AmbientM.invariant _)))
    | (maintenance_head Pure.pure; exact PrefixEnsures.pure c.safe (fun _ _ hi => hi))
    | (maintenance_head Bind.bind; apply PrefixEnsures.bind (Q := fun _ => I))
    | maintenance_match
    | maintenance_intro
    | contradiction
    | maintenance_impossible_match

theorem handshakeSendWorkerPrefix_preserves_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner)))))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (handshakeSendWorkerPrefix pid)) := by
  unfold handshakeSendWorkerPrefix
  rw [liftWGObserver_bind]
  exact PrefixPreserves.bind (sendHandshakeInitiationPrefix_preserves_product c sc hi pid) (fun _ => c.peerPut _)

inductive HandshakeSendCall where
  | buffer (pid : PeerId) (bytes : List UInt8)
  | sessionDerived (pid : PeerId)
  | initiated (pid : PeerId)
  | initiation (pid : PeerId)
  | response (pid : PeerId)
  | worker (pid : PeerId)

namespace HandshakeSendCall

def original : HandshakeSendCall → WG.M Unit
  | .buffer pid bytes => sendBufferToPeer pid bytes
  | .sessionDerived pid => timersSessionDerived pid
  | .initiated pid => timersHandshakeInitiated pid
  | .initiation pid => sendHandshakeInitiation pid
  | .response pid => sendHandshakeResponse pid
  | .worker pid => handshakeSendWorker pid

def observed : HandshakeSendCall → MixedM Unit
  | .buffer pid bytes => sendBufferToPeerPrefix pid bytes
  | .sessionDerived pid => timersSessionDerivedPrefix pid
  | .initiated pid => timersHandshakeInitiatedPrefix pid
  | .initiation pid => sendHandshakeInitiationPrefix pid
  | .response pid => sendHandshakeResponsePrefix pid
  | .worker pid => handshakeSendWorkerPrefix pid

theorem erases (call : HandshakeSendCall) : ErasesStatePrefix call.observed call.original := by
  cases call with
  | buffer pid bytes => exact sendBufferToPeerPrefix_erases pid bytes
  | sessionDerived pid => exact timersSessionDerivedPrefix_erases pid
  | initiated pid => exact timersHandshakeInitiatedPrefix_erases pid
  | initiation pid => exact sendHandshakeInitiationPrefix_erases pid
  | response pid => exact sendHandshakeResponsePrefix_erases pid
  | worker pid => exact handshakeSendWorkerPrefix_erases pid

theorem preserves_ambient (c : AmbientContracts I) (sc : SocketContracts I)
    (hi : ∀ owner, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexInsert owner))))
    (create : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairCreatePrefix pid))
    (put : ∀ kp now, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keypairPutPrefix kp now))
    (replace : ∀ pid kp, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp))))
    (call : HandshakeSendCall) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe call.observed := by
  cases call with
  | buffer pid bytes => exact AmbientContracts.drop (sendBufferToPeerPrefix_spec c sc (fun _ => True) pid bytes)
  | sessionDerived pid => exact AmbientContracts.drop (timersSessionDerivedPrefix_spec c (fun _ => True) pid)
  | initiated pid => exact AmbientContracts.drop (timersHandshakeInitiatedPrefix_spec c (fun _ => True) pid)
  | initiation pid => exact sendHandshakeInitiationPrefix_preserves c sc hi pid
  | response pid => exact sendHandshakeResponsePrefix_preserves c sc hi create put replace pid
  | worker pid => exact handshakeSendWorkerPrefix_preserves c sc hi pid

theorem preserves_ambient_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I)
    (hi : ∀ owner, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexInsert owner)))))
    (create : ∀ pid, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairCreatePrefix pid)))
    (put : ∀ kp now, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keypairPutPrefix kp now)))
    (replace : ∀ pid kp, PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (liftWGPrefix (liftIndex (indexReplaceHandshake pid kp)))))
    (call : HandshakeSendCall) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver call.observed) := by
  cases call with
  | buffer pid bytes => exact ProductAmbientContracts.drop (sendBufferToPeerPrefix_spec_product c sc (fun _ => True) pid bytes)
  | sessionDerived pid => exact ProductAmbientContracts.drop (timersSessionDerivedPrefix_spec_product c (fun _ => True) pid)
  | initiated pid => exact ProductAmbientContracts.drop (timersHandshakeInitiatedPrefix_spec_product c (fun _ => True) pid)
  | initiation pid => exact sendHandshakeInitiationPrefix_preserves_product c sc hi pid
  | response pid => exact sendHandshakeResponsePrefix_preserves_product c sc hi create put replace pid
  | worker pid => exact handshakeSendWorkerPrefix_preserves_product c sc hi pid

theorem allocation (call : HandshakeSendCall) :
    StatePrefixPreserves (fun h w _ => AllocationInv h w) LifetimeEvent.Safe call.observed := by
  apply call.preserves_ambient allocationAmbient allocationSocket ?_ keypairCreatePrefix_preserves
    keypairPutPrefix_allocation indexReplaceHandshake_allocation
  intro owner
  apply StatePrefixEnsures.lift _ (fun h w _ hi => hi.safe)
  intro h w ambient x v ambient' hi hr
  have hp : Hoare (liftIndex (indexInsert owner)) (AllocationInv h) (fun _ => AllocationInv h) := by
    apply hoare_liftIndex
    intro g d table hg hd
    apply hg.congr
    · unfold identityView Peers.snapshot keypairResidents packetResidents
      simp [hd]
    · simp [allocationMetadata, deviceAllocationMetadata, hd]
  exact (hoare_iff_run_ambient _ _ _).mp hp w ambient x v ambient' hi hr

end HandshakeSendCall
end Leanux.Proofs.WG.Lifetimes
