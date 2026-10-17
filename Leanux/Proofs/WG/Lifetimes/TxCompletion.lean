import Leanux.Proofs.WG.Lifetimes.SocketCalls
import Leanux.Proofs.WG.Lifetimes.ReceiveCompletion

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Complete TX completion helpers. Socket transmission uses the concrete
IPv4/IPv6 observers, including loopback's saved-peer scan. Ordinary send errors
remain Boolean results; Stops retain all preceding resolved accesses. -/
namespace Leanux.Proofs.WG.Lifetimes
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do

def sendSkbToPeerPrefix (pid : PeerId) (bytes : List UInt8) (ds : Nat) : MixedM Bool := do
  let p ← getPeerMixed pid
  let family := (p.endpoint.map (·.family)).getD 0
  let e := p.endpoint.getD {family := 0, addr := 0, port := 0}
  let ret ← do
    if ← liftWGPrefix (branch .sendSkbInet (family == AF_INET)) then send4Prefix e (some pid) bytes ds true
    else if ← liftWGPrefix (branch .sendSkbInet6 (family == AF_INET6)) then send6Prefix e (some pid) bytes ds true
    else pure (-EAFNOSUPPORT)
  let sent := ret == 0
  if ← liftWGPrefix (branch .sendSkbOk sent) then
    modifyPeerKeysPrefix pid fun p => {p with txBytes := p.txBytes + bytes.length}
  return sent

def timersDataSentPrefix (pid : PeerId) : MixedM Unit := do
  if ← liftWGPrefix (branch .timersDataSentNotPending !((← getPeerMixed pid).timerPending .newHandshake)) then
    let jc ← liftWGPrefix (callerJiffies .timerJiffiesDataSent)
    let jitter ← liftWGPrefix (jitterBelowRekeyTimeout .newHandshakeJitter)
    if ← modPeerTimerGuardPrefix pid then
      armTimerPrefix pid .newHandshake (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter) jc

def timersAnyAuthenticatedPacketSentPrefix (pid : PeerId) : MixedM Unit :=
  delTimerPrefix pid .sendKeepalive

def keepKeyFreshPrefix (pid : PeerId) : MixedM Unit := do
  let current := (← getPeerMixed pid).keypairCurrent
  let send ← andPrefix (liftWGPrefix (branch .freshKeypair current.isSome)) do
    let some id := current | liftWGPrefix (invariant "unreachable")
    let k ← getKeypairPrefix id
    andPrefix (liftWGPrefix (branch .freshValid k.sending.isValid)) do
      orPrefix (liftWGPrefix (branchCmp .freshCounter (k.sendingCounter > REKEY_AFTER_MESSAGES)
        k.sendingCounter REKEY_AFTER_MESSAGES)) do
        andPrefix (liftWGPrefix (branch .freshInitiator k.iAmTheInitiator)) do
          liftWGPrefix (branchExpired .freshExpired k.sending.birthdate REKEY_AFTER_TIME)
  if ← liftWGPrefix (branch .freshSend send) then sendQueuedHandshakeInitiationPrefix pid false

def createDataDonePrefix (pid : PeerId) (item : List SkbId) : MixedM Unit := do
  timersTraversalPrefix pid
  timersAnyAuthenticatedPacketSentPrefix pid
  let mut dataSent := false
  for id in item do
    let skb ← getTxSkbPrefix id
    _ ← liftWGPrefix (branch .doneSkbIterate true)
    let isKeepalive := skb.bytes.length == MESSAGE_DATA_LEN_0
    let sent ← sendSkbToPeerPrefix pid skb.bytes skb.ds
    if ← andPrefix (liftWGPrefix (branch .doneSendOk sent))
        (liftWGPrefix (branch .doneNotKeepalive !isKeepalive)) then dataSent := true
  _ ← liftWGPrefix (branch .doneSkbIterate false)
  if ← liftWGPrefix (branch .doneDataSent dataSent) then timersDataSentPrefix pid
  keepKeyFreshPrefix pid

theorem sendSkbToPeerPrefix_erases (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    ErasesStatePrefix (sendSkbToPeerPrefix pid bytes ds) (sendSkbToPeer pid bytes ds) := by
  unfold sendSkbToPeerPrefix sendSkbToPeer modifyPeerKeysPrefix
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head getTxSkbPrefix; exact getTxSkbPrefix_erases _)
    | (maintenance_head send4Prefix; exact send4Prefix_erases _ _ _ _ _)
    | (maintenance_head send6Prefix; exact send6Prefix_erases _ _ _ _ _)
    | (maintenance_head modPeerTimerGuardPrefix; exact modPeerTimerGuardPrefix_erases _)
    | (maintenance_head armTimerPrefix; exact armTimerPrefix_erases _ _ _ _)
    | (maintenance_head timersTraversalPrefix; exact timersTraversalPrefix_erases _)
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact timersAnyAuthenticatedPacketSentPrefix_erases _)
    | (maintenance_head timersDataSentPrefix; exact timersDataSentPrefix_erases _)
    | (maintenance_head keepKeyFreshPrefix; exact keepKeyFreshPrefix_erases _)
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head andPrefix; apply andPrefix_erases_state)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | maintenance_erases_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem timersDataSentPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (timersDataSentPrefix pid) (timersDataSent pid) := by
  unfold timersDataSentPrefix timersDataSent
  try simp (config := { zeta := false }) only [bind_assoc]
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head getTxSkbPrefix; exact getTxSkbPrefix_erases _)
    | (maintenance_head send4Prefix; exact send4Prefix_erases _ _ _ _ _)
    | (maintenance_head send6Prefix; exact send6Prefix_erases _ _ _ _ _)
    | (maintenance_head modPeerTimerGuardPrefix; exact modPeerTimerGuardPrefix_erases _)
    | (maintenance_head armTimerPrefix; exact armTimerPrefix_erases _ _ _ _)
    | (maintenance_head timersTraversalPrefix; exact timersTraversalPrefix_erases _)
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact timersAnyAuthenticatedPacketSentPrefix_erases _)
    | (maintenance_head keepKeyFreshPrefix; exact keepKeyFreshPrefix_erases _)
    | (maintenance_head sendSkbToPeerPrefix; exact sendSkbToPeerPrefix_erases _ _ _)
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head andPrefix; apply andPrefix_erases_state)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | maintenance_erases_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem timersAnyAuthenticatedPacketSentPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (timersAnyAuthenticatedPacketSentPrefix pid) (timersAnyAuthenticatedPacketSent pid) :=
  delTimerPrefix_erases pid .sendKeepalive

theorem keepKeyFreshPrefix_erases (pid : PeerId) :
    ErasesStatePrefix (keepKeyFreshPrefix pid) (keepKeyFresh pid) := by
  unfold keepKeyFreshPrefix keepKeyFresh
  apply erasesStatePrefix_bind (getPeerMixed_erases pid)
  intro p
  apply erasesStatePrefix_bind
  · apply andPrefix_erases_state (erasesStatePrefix_lift _)
    cases he : p.keypairCurrent with
    | none => exact erasesStatePrefix_lift _
    | some id =>
      apply erasesStatePrefix_bind (getKeypairPrefix_erases id)
      intro k
      exact andPrefix_erases_state (erasesStatePrefix_lift _)
        (orPrefix_erases_state (erasesStatePrefix_lift _)
          (andPrefix_erases_state (erasesStatePrefix_lift _) (erasesStatePrefix_lift _)))
  · intro send
    apply erasesStatePrefix_bind (erasesStatePrefix_lift _)
    intro yes
    split
    · exact sendQueuedHandshakeInitiationPrefix_erases pid false
    · exact erasesStatePrefix_pure _

theorem createDataDonePrefix_erases (pid : PeerId) (item : List SkbId) :
    ErasesStatePrefix (createDataDonePrefix pid item) (createDataDone pid item) := by
  unfold createDataDonePrefix createDataDone
  try simp (config := { zeta := false }) only []
  repeat' first
    | maintenance_erases_join
    | maintenance_erases_join_use
    | (maintenance_head getPeerMixed; exact getPeerMixed_erases _)
    | (maintenance_head setPeerMixed; exact setPeerMixed_erases _ _)
    | (maintenance_head getTxSkbPrefix; exact getTxSkbPrefix_erases _)
    | (maintenance_head send4Prefix; exact send4Prefix_erases _ _ _ _ _)
    | (maintenance_head send6Prefix; exact send6Prefix_erases _ _ _ _ _)
    | (maintenance_head modPeerTimerGuardPrefix; exact modPeerTimerGuardPrefix_erases _)
    | (maintenance_head armTimerPrefix; exact armTimerPrefix_erases _ _ _ _)
    | (maintenance_head timersTraversalPrefix; exact timersTraversalPrefix_erases _)
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact timersAnyAuthenticatedPacketSentPrefix_erases _)
    | (maintenance_head timersDataSentPrefix; exact timersDataSentPrefix_erases _)
    | (maintenance_head keepKeyFreshPrefix; exact keepKeyFreshPrefix_erases _)
    | (maintenance_head sendSkbToPeerPrefix; exact sendSkbToPeerPrefix_erases _ _ _)
    | (maintenance_lift_head; exact erasesStatePrefix_lift _)
    | (maintenance_head Pure.pure; exact erasesStatePrefix_pure _)
    | (maintenance_head andPrefix; apply andPrefix_erases_state)
    | (maintenance_head ForIn.forIn; apply erasesStatePrefix_forIn)
    | maintenance_erases_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem sendSkbToPeerPrefix_spec (c : AmbientContracts I) (sc : SocketContracts I)
    (P : IdentityView → Prop) (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    AmbientSpec I P (sendSkbToPeerPrefix pid bytes ds) (fun _ => P) := by
  unfold sendSkbToPeerPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head send4Prefix; exact send4Prefix_spec c sc P _ _ _ _ _)
    | (maintenance_head send6Prefix; exact send6Prefix_spec c sc P _ _ _ _ _)
    | (maintenance_head modPeerTimerGuardPrefix; exact modPeerTimerGuardPrefix_spec c P _)
    | (maintenance_head armTimerPrefix; exact armTimerPrefix_spec c P _ _ _ _)
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head callerJiffies; exact c.store P _ ((callerJiffies_sameWGWorld _).factor wgStoreView))
    | (maintenance_lift_action_head jitterBelowRekeyTimeout; exact c.store P _ ((jitterBelowRekeyTimeout_sameWGWorld _).factor wgStoreView))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem timersDataSentPrefix_spec (c : AmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (timersDataSentPrefix pid) (fun _ => P) := by
  unfold timersDataSentPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head send4Prefix; exact send4Prefix_spec c sc P _ _ _ _ _)
    | (maintenance_head send6Prefix; exact send6Prefix_spec c sc P _ _ _ _ _)
    | (maintenance_head modPeerTimerGuardPrefix; exact modPeerTimerGuardPrefix_spec c P _)
    | (maintenance_head armTimerPrefix; exact armTimerPrefix_spec c P _ _ _ _)
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_ambient c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head callerJiffies; exact c.store P _ ((callerJiffies_sameWGWorld _).factor wgStoreView))
    | (maintenance_lift_action_head jitterBelowRekeyTimeout; exact c.store P _ ((jitterBelowRekeyTimeout_sameWGWorld _).factor wgStoreView))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem timersAnyAuthenticatedPacketSentPrefix_spec (c : AmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    AmbientSpec I P (timersAnyAuthenticatedPacketSentPrefix pid) (fun _ => P) :=
  delTimerPrefix_spec c P pid .sendKeepalive

theorem keepKeyFreshPrefix_preserves (c : AmbientContracts I)
    (hq : ∀ pid, StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe
      (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})))
    (pid : PeerId) : StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (keepKeyFreshPrefix pid) := by
  unfold keepKeyFreshPrefix andPrefix orPrefix
  unfold StatePrefixPreserves
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head getPeerMixed; exact AmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head getKeypairPrefix; exact AmbientContracts.drop (c.getKeypair_frame (fun _ => True) _))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.branch (fun _ => True) _ _))
    | (maintenance_lift_action_head branchCmp; exact AmbientContracts.drop (c.branchCmp (fun _ => True) _ _ _ _))
    | (maintenance_lift_action_head invariant; exact AmbientContracts.drop (c.invariant (fun _ => True) _))
    | (maintenance_lift_action_head branchExpired; exact AmbientContracts.drop (c.store (fun _ => True) _ ((branchExpired_sameWGWorld _ _ _ _).factor wgStoreView)))
    | (maintenance_head sendQueuedHandshakeInitiationPrefix; exact sendQueuedHandshakeInitiationPrefix_preserves_ambient c hq _ _)
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

/-- The actual product adapter distributes over a native observer loop. -/
theorem liftWGObserver_forIn {E α β : Type} (xs : List α) (init : β)
    (f : α → β → WGPrefix E (ForInStep β)) :
    liftWGObserver (forIn xs init f) =
      forIn xs init (fun x b => liftWGObserver (f x b)) := by
  induction xs generalizing init with
  | nil => simp only [List.forIn_nil, liftWGObserver_pure]
  | cons x xs ih =>
    simp only [List.forIn_cons, liftWGObserver_bind]
    congr 1
    funext step
    cases step with
    | done b => exact liftWGObserver_pure b
    | yield b => exact ih b

theorem createDataDonePrefix_preserves (c : AmbientContracts I) (t : TxContracts I)
    (sc : SocketContracts I) (pid : PeerId) (item : List SkbId) :
    StatePrefixPreserves (fun h w _ => I h w) LifetimeEvent.Safe (createDataDonePrefix pid item) := by
  have fresh := keepKeyFreshPrefix_preserves c
    (fun pid => AmbientContracts.drop (t.device (fun _ => True) (.handshake pid))) pid
  have loop_preserves {α β : Type} (xs : List α) (b : β)
      (g : α → β → MixedM (ForInStep β))
      (hg : ∀ x b, StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe (g x b) (fun _ h w _ => I h w)) :
      StatePrefixEnsures (fun h w _ => I h w) LifetimeEvent.Safe (forIn xs b g) (fun _ h w _ => I h w) :=
    StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => I h w) LifetimeEvent.Safe
      (fun _ h w _ hi => c.safe h w hi) hg
  unfold createDataDonePrefix andPrefix
  unfold StatePrefixPreserves
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head timersTraversalPrefix; exact AmbientContracts.drop (timersTraversalPrefix_spec c (fun _ => True) _))
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact AmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec c (fun _ => True) _))
    | (maintenance_head timersDataSentPrefix; exact AmbientContracts.drop (timersDataSentPrefix_spec c (fun _ => True) _))
    | (maintenance_head sendSkbToPeerPrefix; exact AmbientContracts.drop (sendSkbToPeerPrefix_spec c sc (fun _ => True) _ _ _))
    | (maintenance_head keepKeyFreshPrefix; exact fresh)
    | (maintenance_head getTxSkbPrefix; exact AmbientContracts.drop (t.get (fun _ => True) _))
    | (maintenance_lift_action_head branch; exact AmbientContracts.drop (c.branch (fun _ => True) _ _))
    | (maintenance_head Pure.pure; exact StatePrefixEnsures.pure _ (fun h w _ hi => c.safe h w hi) (fun _ _ _ hi => hi))
    | (maintenance_head ForIn.forIn; apply loop_preserves)
    | maintenance_spec_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

/-- A jitter failure occurs after the pending-timer read and before the timer
guard. Premises describe consecutive original runs, not a desired log. -/
theorem timersDataSentPrefix_jitter_failure (pid : PeerId) (w entered clocked : WGWorld) (ambient enteredAmbient clockedAmbient : Ambient) (jc : Option UInt64)
    (p : Peer) (h : List LifetimeEvent) (e : Stop)
    (hp : ((getPeer pid).run w).run ambient = .ok ((p, w), ambient))
    (hb : ((branch .timersDataSentNotPending !(p.timerPending .newHandshake) : WG.M Bool).run w).run ambient = .ok ((true, entered), enteredAmbient))
    (hc : ((callerJiffies .timerJiffiesDataSent).run entered).run enteredAmbient = .ok ((jc, clocked), clockedAmbient))
    (hj : ((jitterBelowRekeyTimeout .newHandshakeJitter).run clocked).run clockedAmbient = .error e) :
    runStatePrefix (timersDataSentPrefix pid) w ambient h = (.error e, h ++ [.peer (.read pid p.internalId)]) := by
  simp only [timersDataSentPrefix, runStatePrefix_bind, getPeerMixed_run, hp,
    runStatePrefix_lift, liftWGPrefix, hb, ↓reduceIte, hc, hj]

theorem sendSkbToPeerPrefix_spec_product (c : ProductAmbientContracts I) (sc : ProductSocketContracts I)
    (P : IdentityView → Prop) (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    ProductAmbientSpec I P (liftWGObserver (sendSkbToPeerPrefix pid bytes ds)) (fun _ => P) := by
  unfold sendSkbToPeerPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head send4Prefix; exact send4Prefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head send6Prefix; exact send6Prefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head modPeerTimerGuardPrefix; exact modPeerTimerGuardPrefix_spec_product c P _)
    | (maintenance_head armTimerPrefix; exact armTimerPrefix_spec_product c P _ _ _ _)
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head callerJiffies; exact c.nativeStore P _ ((callerJiffies_sameWGWorld _).factor wgStoreView))
    | (maintenance_lift_action_head jitterBelowRekeyTimeout; exact c.nativeStore P _ ((jitterBelowRekeyTimeout_sameWGWorld _).factor wgStoreView))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem timersDataSentPrefix_spec_product (c : ProductAmbientContracts I) (P : IdentityView → Prop) (pid : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (timersDataSentPrefix pid)) (fun _ => P) := by
  unfold timersDataSentPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head send4Prefix; exact send4Prefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head send6Prefix; exact send6Prefix_spec_product c sc P _ _ _ _ _)
    | (maintenance_head modPeerTimerGuardPrefix; exact modPeerTimerGuardPrefix_spec_product c P _)
    | (maintenance_head armTimerPrefix; exact armTimerPrefix_spec_product c P _ _ _ _)
    | (maintenance_head getPeerMixed; exact c.getPeer_frame P _)
    | (maintenance_head modifyPeerKeysPrefix; exact modifyPeerKeysPrefix_spec_product c P _ _ (fun _ => rfl))
    | (maintenance_lift_action_head branch; exact c.branch P _ _)
    | (maintenance_lift_action_head callerJiffies; exact c.nativeStore P _ ((callerJiffies_sameWGWorld _).factor wgStoreView))
    | (maintenance_lift_action_head jitterBelowRekeyTimeout; exact c.nativeStore P _ ((jitterBelowRekeyTimeout_sameWGWorld _).factor wgStoreView))
    | (maintenance_head Pure.pure; exact c.pure P _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem timersAnyAuthenticatedPacketSentPrefix_spec_product (c : ProductAmbientContracts I)
    (P : IdentityView → Prop) (pid : PeerId) :
    ProductAmbientSpec I P (liftWGObserver (timersAnyAuthenticatedPacketSentPrefix pid)) (fun _ => P) :=
  delTimerPrefix_spec_product c P pid .sendKeepalive

theorem keepKeyFreshPrefix_preserves_product (c : ProductAmbientContracts I)
    (hq : ∀ pid, PrefixPreserves I LifetimeEvent.Safe
      (liftWGObserver (liftWGPrefix (modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]}))))
    (pid : PeerId) : PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (keepKeyFreshPrefix pid)) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixEnsures I LifetimeEvent.Safe
        (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => I) := by
    rw [liftWGObserver_lift, liftWG_ambient]
    exact ProductAmbientContracts.drop (c.ambient (fun _ => True) a)
  change PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (keepKeyFreshPrefix pid)) (fun _ => I)
  unfold keepKeyFreshPrefix andPrefix orPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | maintenance_product_lift
    | (maintenance_head getPeerMixed; exact ProductAmbientContracts.drop (c.getPeer_frame (fun _ => True) _))
    | (maintenance_head getKeypairPrefix; exact ProductAmbientContracts.drop (c.getKeypair_frame (fun _ => True) _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_lift_action_head branchCmp; exact ambient (AmbientM.branchCmp _ _ _ _))
    | (maintenance_lift_action_head invariant; exact ambient (AmbientM.invariant _))
    | (maintenance_lift_action_head branchExpired; exact ProductAmbientContracts.drop (c.nativeStore (fun _ => True) _ ((branchExpired_sameWGWorld _ _ _ _).factor wgStoreView)))
    | (maintenance_head sendQueuedHandshakeInitiationPrefix; exact sendQueuedHandshakeInitiationPrefix_preserves_product c hq _ _)
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

theorem createDataDonePrefix_preserves_product (c : ProductAmbientContracts I) (t : ProductTxContracts I)
    (sc : ProductSocketContracts I) (pid : PeerId) (item : List SkbId) :
    PrefixPreserves I LifetimeEvent.Safe (liftWGObserver (createDataDonePrefix pid item)) := by
  have ambient {α : Type} (a : AmbientM α) :
      PrefixEnsures I LifetimeEvent.Safe
        (liftWGObserver (liftWGPrefix (StateT.lift a))) (fun _ => I) := by
    rw [liftWGObserver_lift, liftWG_ambient]
    exact ProductAmbientContracts.drop (c.ambient (fun _ => True) a)
  have fresh := keepKeyFreshPrefix_preserves_product c
    (fun pid => ProductAmbientContracts.drop (t.device (fun _ => True) (.handshake pid))) pid
  have loop_preserves {α β : Type} (xs : List α) (b : β)
      (g : α → β → PrefixM LifetimeEvent (ForInStep β))
      (hg : ∀ x b, PrefixEnsures I LifetimeEvent.Safe (g x b) (fun _ => I)) :
      PrefixEnsures I LifetimeEvent.Safe (forIn xs b g) (fun _ => I) :=
    PrefixEnsures.forInInvariant xs b g (fun _ => I) LifetimeEvent.Safe
      (fun _ h w hi => c.safe h w hi) hg
  change PrefixEnsures I LifetimeEvent.Safe (liftWGObserver (createDataDonePrefix pid item)) (fun _ => I)
  unfold createDataDonePrefix andPrefix
  repeat' first
    | maintenance_join_let
    | maintenance_join_use
    | (maintenance_head ForIn.forIn; rw [liftWGObserver_forIn])
    | maintenance_product_lift
    | (maintenance_head timersTraversalPrefix; exact ProductAmbientContracts.drop (timersTraversalPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head timersAnyAuthenticatedPacketSentPrefix; exact ProductAmbientContracts.drop (timersAnyAuthenticatedPacketSentPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head timersDataSentPrefix; exact ProductAmbientContracts.drop (timersDataSentPrefix_spec_product c (fun _ => True) _))
    | (maintenance_head sendSkbToPeerPrefix; exact ProductAmbientContracts.drop (sendSkbToPeerPrefix_spec_product c sc (fun _ => True) _ _ _))
    | (maintenance_head keepKeyFreshPrefix; exact fresh)
    | (maintenance_head getTxSkbPrefix; exact ProductAmbientContracts.drop (t.get (fun _ => True) _))
    | (maintenance_lift_action_head branch; exact ambient (AmbientM.branch _ _))
    | (maintenance_head Pure.pure; exact PrefixPreserves.pure c.safe _)
    | (maintenance_head ForIn.forIn; apply loop_preserves)
    | maintenance_product_bind
    | maintenance_intro
    | maintenance_reduce
    | (maintenance_head ite; split)
    | maintenance_reduce_match
    | maintenance_match
    | maintenance_impossible_match
    | contradiction

end Leanux.Proofs.WG.Lifetimes
