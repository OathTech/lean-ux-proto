import Leanux.Proofs.WG.AllowedIps.RoutingSocketFrames

/-! Concrete routing frames for the handshake/clear work executed by peer
removal. Only actual normal returns carry a frame; recorded failures stay intact. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1200000
set_option pp.structureInstances false

theorem modifyPeer_routing (pid : PeerId) (f : Peer → Peer)
    (hl : ∀ p, (f p).allowedipsList = p.allowedipsList) :
    SameView routingView (do let p ← getPeer pid; setPeer pid (f p)) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  mvcgen [hg, hs]
  all_goals simp_all []

theorem setPeerEndpoint_routing (pid : PeerId) (e : Endpoint) : SameView routingView (setPeerEndpoint pid e) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hc := (dstCacheReset_routing pid).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) (P : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) P (fun _ => P) := hoare_liftAmbient a P
  unfold Hoare at ambient
  have he (old : Option Endpoint) :
      ⦃fun w => ⌜routingView w = s⌝⦄ endpointEq e old ⦃⇓? _ w => ⌜routingView w = s⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, endpointEq, WG.andM, branch, ambient]
    all_goals simp_all
  mvcgen [-Std.Do.Spec.monadLift_StateT, setPeerEndpoint, he, hg, hs, hc,
    requireNotPending, branch, ambient]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [routingView]

theorem armTimer_routing (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView routingView (armTimer pid timer delay jc) := by
  have wheel (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameView routingView (placeOnWheel pid t expires clk unit) := by
    apply SameView.of_wp
    intro s
    have hg := routing_getPeer (fun q => q = s) pid
    have hs := fun p => routing_setPeer (fun q => q = s) pid p
    have ambient {α : Type} (a : AmbientM α) (P : WGWorld → Prop) :
        Hoare (MonadLift.monadLift a : WG.M α) P (fun _ => P) := hoare_liftAmbient a P
    unfold Hoare at ambient
    mvcgen [-Std.Do.Spec.monadLift_StateT, placeOnWheel, hg, hs, ambient,
      hidden, peekHiddenSite, invariant]
    all_goals have timer_list (p : Peer) (e : Option UInt64) :
        (p.setTimer t e).allowedipsList = p.allowedipsList := by cases t <;> rfl
    all_goals have wheel_list (p : Peer) (e : Option WheelEntry) :
        (p.setWheel t e).allowedipsList = p.allowedipsList := by cases t <;> rfl
    all_goals try dsimp +zetaDelta only [routingView]
    all_goals simp_all [routingView]

  have ambient {α : Type} (a : AmbientM α) : SameView routingView (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => routingView w = initial)
  have read : SameView routingView (get : WG.M WGWorld) := by
    apply SameView.of_wp; intro initial; mvcgen
  have dev : SameView routingView getDev := by
    apply SameView.of_wp; intro initial; mvcgen [getDev, invariant, AmbientM.invariant]
  have stopped {α : Type} (e : Stop) : SameView routingView (throw e : WG.M α) := by
    apply SameView.of_wp; intro initial; mvcgen
  have edit (f : WGWorld → WGWorld) (hf : ∀ w, routingView (f w) = routingView w) :
      SameView routingView (modify f : WG.M Unit) := by
    intro initial
    apply hoare_modify
    intro w hw
    exact (hf w).trans hw
  unfold armTimer
  simp (config := { zeta := false }) only [getAmbient, hidden, invariant, unsupported]
  repeat' first
    | rxqueue_join_let
    | rxqueue_join_use
    | (snapshot_head placeOnWheel; exact wheel _ _ _ _)
    | (snapshot_head getDev; exact dev)
    | (snapshot_head getPeer; exact getPeer_routing _)
    | (snapshot_head MonadLiftT.monadLift; exact ambient _)
    | (snapshot_head MonadLift.monadLift; exact ambient _)
    | (snapshot_head get; exact read)
    | (snapshot_head MonadStateOf.get; exact read)
    | (snapshot_head throw; exact stopped _)
    | (snapshot_head MonadExceptOf.throw; exact stopped _)
    | contradiction
    | keypairs_intro_forall
    | (snapshot_head Pure.pure; exact SameView.pure _ _)
    | (snapshot_head Bind.bind; apply SameView.bind)
    | (snapshot_head ite; split)
    | (snapshot_head modify; exact edit _ (fun _ => rfl))
    | snapshot_head_reduce
    | snapshot_head_match

theorem delTimer_routing (pid : PeerId) (timer : PeerTimer) : SameView routingView (delTimer pid timer) :=
  modifyPeer_routing pid (fun p => (p.setTimer timer none).setWheel timer none)
    (fun p => by cases timer <;> rfl)

theorem modPeerTimerGuard_routing (pid : PeerId) : SameView routingView (modPeerTimerGuard pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_routing pid).wp (fun t => t = s)
  mvcgen [modPeerTimerGuard, getDev, hg, WG.andM, branch, AmbientM.branch, invariant, AmbientM.invariant]

theorem modPeerTimer_routing (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView routingView (modPeerTimer site pid timer delay) := by
  apply SameView.of_wp
  intro s
  have hg := (modPeerTimerGuard_routing pid).wp (fun t => t = s)
  have ha := fun jc => (armTimer_routing pid timer delay jc).wp (fun t => t = s)
  have hc := (callerJiffies_sameWGWorld site).wp (fun w => routingView w = s)
  mvcgen [modPeerTimer, hg, ha, hc]

theorem timersTraversal_routing (pid : PeerId) : SameView routingView (timersTraversal pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_routing pid).wp (fun t => t = s)
  have ht := fun delay => (modPeerTimer_routing .timerJiffiesTraversal pid .persistentKeepalive delay).wp (fun t => t = s)
  have hd := fun delay => discard_view_spec (m := AmbientM) routingView (fun t => t = s) _ (ht delay)
  mvcgen [timersTraversal, hg, ht, hd, branchCmp, AmbientM.branchCmp]


theorem timersAnyAuthenticatedPacketSent_routing (pid : PeerId) :
    SameView routingView (timersAnyAuthenticatedPacketSent pid) := delTimer_routing pid .sendKeepalive

theorem timersHandshakeInitiated_routing (pid : PeerId) :
    SameView routingView (timersHandshakeInitiated pid) := by
  apply SameView.of_wp
  intro s
  have hc := (callerJiffies_sameWGWorld .timerJiffiesHandshakeInitiated).wp (fun w => routingView w = s)
  have hj := (jitterBelowRekeyTimeout_sameWGWorld .retransmitJitter).wp (fun w => routingView w = s)
  have hg := (modPeerTimerGuard_routing pid).wp (fun t => t = s)
  have ha := fun n jc => (armTimer_routing pid .retransmitHandshake n jc).wp (fun t => t = s)
  mvcgen [timersHandshakeInitiated, hc, hj, hg, ha]


theorem createInitiation_routing (pid : PeerId) : SameView routingView (createInitiation pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := fun pid => routing_getPeer (fun t => t = s) pid
  have hs := fun pid p => routing_setPeer (fun t => t = s) pid p
  have hp := fun k => (generatePublic_sameWGWorld k).wp (fun w => routingView w = s)
  have he := fun b e ck h => (messageEphemeral_sameWGWorld b e ck h).wp (fun w => routingView w = s)
  have hd := fun b ck p q => (mixDh_sameWGWorld b ck p q).wp (fun w => routingView w = s)
  have hpre := fun ck p => (mixPrecomputedDh_sameWGWorld ck p).wp (fun w => routingView w = s)
  have index_spec {α : Type} (a : IndexM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => routingView w = s) (fun _ w => routingView w = s) := by
    apply hoare_liftIndex a
    intro w d table hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  unfold Hoare at index_spec
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  have hw := (ownerDeref_routing (.handshake pid)).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, hiddenClock64, liftM, hw, hg, hs, hp, he, hd, hpre, index_spec, getDev, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView, routingState]
  all_goals try assumption

theorem addMacToPacket_routing (pid : PeerId) (msg : List UInt8) :
    SameView routingView (addMacToPacket pid msg) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have he := fun d b n f => (branchExpired_sameWGWorld d b n f).wp (fun w => routingView w = s)
  mvcgen [addMacToPacket, hg, hs, he, branch, AmbientM.branch, WG.andM]
  all_goals simp_all

theorem sendBufferToPeer_routing (pid : PeerId) (bytes : List UInt8) :
    SameView routingView (sendBufferToPeer pid bytes) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) (P : WGWorld → Prop) :
      Hoare (MonadLift.monadLift a : WG.M α) P (fun _ => P) := hoare_liftAmbient a P
  unfold Hoare at ambient
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have h4 := fun e => (send4_routing e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  have h6 := fun e => (send6_routing e (some pid) bytes HANDSHAKE_DSCP true).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, hiddenClock64, sendBufferToPeer, hg, hs, h4, h6, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals try simp_all [routingView]
  all_goals try assumption

theorem sendHandshakeInitiation_routing (pid : PeerId) : SameView routingView (sendHandshakeInitiation pid) := by
  apply SameView.of_wp
  intro s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α)
        (fun w => routingView w = s) (fun _ w => routingView w = s) := hoare_liftAmbient a _
  unfold Hoare at ambient
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have he := fun date => (branchExpired_sameWGWorld .initRateLimited date REKEY_TIMEOUT (!·)).wp (fun w => routingView w = s)
  have hi := (createInitiation_routing pid).wp (fun t => t = s)
  have hm := fun msg => (addMacToPacket_routing pid msg).wp (fun t => t = s)
  have ht := (timersTraversal_routing pid).wp (fun t => t = s)
  have ha := (timersAnyAuthenticatedPacketSent_routing pid).wp (fun t => t = s)
  have hb := fun msg => (sendBufferToPeer_routing pid msg).wp (fun t => t = s)
  have hj := (timersHandshakeInitiated_routing pid).wp (fun t => t = s)
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, hidden, hiddenAlloc, hiddenClock64, liftM, sendHandshakeInitiation, hg, hs, he, hi, hm, ht, ha, hb, hj, branch, AmbientM.branch, invariant, AmbientM.invariant]
  all_goals try simp_all

theorem handshakeZero_routing (pid : PeerId) : SameView routingView (handshakeZero pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  mvcgen [handshakeZero, hg, hs]
  all_goals simp_all

theorem keypairsClear_routing (pid : PeerId) : SameView routingView (keypairsClear pid) := by
  apply SameView.of_wp
  intro s
  have hg := routing_getPeer (fun t => t = s) pid
  have hs := fun p => routing_setPeer (fun t => t = s) pid p
  have hk := fun kp => (keypairPut_routing kp true).wp (fun t => t = s)
  unfold keypairsClear
  index_unfold _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer
  mvcgen [hg, hs, hk]
  all_goals simp_all

theorem handshakeClear_routing (pid : PeerId) : SameView routingView (handshakeClear pid) := by
  apply (ownerDeref_routing (.handshake pid)).bind
  intro _
  apply SameView.bind
  · intro initial
    apply hoare_liftIndex (indexRemove (.handshake pid))
    intro w d table hi hd
    simpa only [routingView, hd, Option.map_some, routingState] using hi
  · intro _
    exact handshakeZero_routing pid

theorem handshakeSendWorker_routing (pid : PeerId) : RetainsRoutingCall (handshakeSendWorker pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hi := (sendHandshakeInitiation_routing pid).wp (RetainsRouting s)
  have hp := RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  mvcgen [handshakeSendWorker, hi, hp]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

theorem queuedExpiredZeroKeyMaterial_routing (pid : PeerId) : RetainsRoutingCall (queuedExpiredZeroKeyMaterial pid) := by
  apply ProjectedAction.of_wp
  intro s
  have hh := (handshakeClear_routing pid).wp (RetainsRouting s)
  have hk := (keypairsClear_routing pid).wp (RetainsRouting s)
  have hp := RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s
  mvcgen [queuedExpiredZeroKeyMaterial, hh, hk, hp]
  all_goals subst s
  all_goals exact RetainsRouting.refl _

end Leanux.Proofs.WG.AllowedIps
