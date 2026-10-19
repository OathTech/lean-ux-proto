import Leanux.Proofs.WG.AllowedIps.RoutingSocketFrames

/-! Concrete routing frames for the handshake/clear work executed by peer
removal. Only actual normal returns carry a frame; recorded failures stay intact. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1200000
set_option pp.structureInstances false


/- Guard action heads before applying checked source-composition rules. -/
open Lean Meta Elab Tactic in
elab "routing_handshake_peer_bind" : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Preserves do throwError "not a routing frame"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.isAppOf ``Bind.bind && action.getAppArgs.size ≥ 2 do throwError "not a bind"
  let first := action.getAppArgs[action.getAppArgs.size - 2]!.consumeMData
  unless first.isAppOf ``getPeer do throwError "not a peer read"

open Lean Meta Elab Tactic in
elab "routing_handshake_fact " n:ident " at " initial:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Preserves do throwError "not a routing frame"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  let proof ← Lean.Elab.Term.elabTerm n none
  let (args, _, conclusion) ← forallMetaTelescope (← instantiateMVars (← inferType proof))
  let conclusion ← instantiateMVars conclusion
  unless conclusion.isAppOf ``SameView do throwError "not a view frame"
  let framed := conclusion.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.constName? == framed.getAppFn.constName? do
    throwError "different routing action"
  let predicate ← Lean.Elab.Term.elabTerm (← `(fun view : Option RoutingState => view = $initial)) none
  let applied ← mkAppM ``SameView.wp #[mkAppN proof args, predicate]
  replaceMainGoal (← withTransparency .default (goal.apply applied))

macro "routing_handshake_source" "[" fs:ident,* "]" "using" "[" facts:ident,* "]" : tactic => do
  let pinned := fs.getElems.map fun f =>
    if f.getId.toString.startsWith "_private." then Lean.mkCIdent (normalizePinnedName f.getId) else f
  let mut use ← `(tactic| fail "no named routing frame")
  for fact in facts.getElems.reverse do
    use ← `(tactic| first | routing_handshake_fact $fact at initial | ($use:tactic))
  let mut atom ← `(tactic| fail "not a native wrapper")
  for name in #[``Leanux.branch, ``Leanux.branchCmp, ``Leanux.branchCmpExcluded,
      ``Leanux.invariant, ``Leanux.unsupported, ``Leanux.hidden, ``Leanux.hiddenAlloc,
      ``Leanux.hiddenClock, ``Leanux.hiddenClock64, ``Leanux.hiddenJiffies,
      ``Leanux.getAmbient, ``Leanux.modifyAmbient, ``Leanux.peekHiddenSite,
      ``Leanux.WG.getDev, ``Leanux.WG.andM, ``Leanux.WG.orM,
      ``Leanux.WG.requireNotPending, ``liftM].reverse do
    let n := Lean.mkCIdent name
    atom ← `(tactic| first | (rx_retention_head $n; unfold $n) | ($atom:tactic))
  let expand ← if pinned.isEmpty then `(tactic| skip) else `(tactic| unfold $pinned:ident*)
  `(tactic|
    (intro initial
     change Preserves (fun w => routingView w = initial) _
     have readBind {α : Type} (pid : PeerId) (f : Peer → WG.M α)
         (hf : ∀ p, initial.bind (fun view => view.lists pid) = some p.allowedipsList →
           Preserves (fun w => routingView w = initial) (f p)) :
         Preserves (fun w => routingView w = initial) (getPeer pid >>= f) := by
       apply hoare_bind _ _ (routing_getPeer (fun view => view = initial) pid)
       intro p
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' h hr
       have saved : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
         simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using h.2
       rw [h.1] at saved
       exact (hoare_iff_run_ambient _ _ _).mp (hf p saved) w ambient x v ambient' h.1 hr
     have knownSet (pid : PeerId) (p : Peer)
         (hp : initial.bind (fun view => view.lists pid) = some p.allowedipsList) :
         Preserves (fun w => routingView w = initial) (setPeer pid p) := by
       apply hoare_consequence (routing_setPeer (fun view => view = initial) pid p)
       · intro w h
         refine ⟨h, ?_⟩
         have current : (routingView w).bind (fun view => view.lists pid) = some p.allowedipsList := by
           rw [h]; exact hp
         simpa only [routingView, routingState, Option.bind_map, Function.comp_def] using current
       · exact fun _ _ h => h
     have ambient {α : Type} (a : AmbientM α) :
         Preserves (fun w => routingView w = initial) (monadLift a : WG.M α) :=
       hoare_liftAmbient a _
     have index {α : Type} (a : IndexM α) :
         Preserves (fun w => routingView w = initial) (monadLift a : WG.M α) := by
       apply hoare_liftIndex a
       intro w d table hi hd
       simpa only [routingView, hd, Option.map_some, routingState] using hi
     have mapped {α β : Type} (f : α → β) (a : WG.M α)
         (ha : Preserves (fun w => routingView w = initial) a) :
         Preserves (fun w => routingView w = initial) (f <$> a) :=
       map_view_spec routingView (fun view => view = initial) f a ha
     have read : Preserves (fun w => routingView w = initial) (get : WG.M WGWorld) :=
       hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2)
     have stopped {α : Type} (e : Stop) :
         Preserves (fun w => routingView w = initial) (throw e : WG.M α) := by
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' _ hr
       cases hr
     have timer_list (p : Peer) (t : PeerTimer) (e : Option UInt64) :
         (p.setTimer t e).allowedipsList = p.allowedipsList := by cases t <;> rfl
     have wheel_list (p : Peer) (t : PeerTimer) (e : Option WheelEntry) :
         (p.setWheel t e).allowedipsList = p.allowedipsList := by cases t <;> rfl
     $expand
     repeat' first
       | ($use:tactic)
       | (routing_handshake_peer_bind; apply readBind; intro p hp)
       | (rx_retention_head setPeer; apply knownSet; simpa only [timer_list, wheel_list] using hp)
       | routing_handshake_fact getPeer_routing at initial
       | routing_handshake_fact getKeypair_routing at initial
       | routing_handshake_fact ownerDeref_routing at initial
       | routing_handshake_fact ownerWord_routing at initial
       | ($atom:tactic)
       | (rx_retention_head MonadLiftT.monadLift; first | exact ambient _ | exact index _)
       | (rx_retention_head MonadLift.monadLift; first | exact ambient _ | exact index _)
       | (rx_retention_head get; exact read)
       | (rx_retention_head MonadStateOf.get; exact read)
       | (rx_retention_head throw; exact stopped _)
       | (rx_retention_head MonadExceptOf.throw; exact stopped _)
       | (rx_retention_head modify; apply hoare_modify; intro w h; exact h)
       | (rx_retention_head Functor.discard; apply mapped)
       | (rx_retention_head Functor.mapConst; apply mapped)
       | rx_retention_step))

theorem modifyPeer_routing (pid : PeerId) (f : Peer → Peer)
    (hl : ∀ p, (f p).allowedipsList = p.allowedipsList) :
    SameView routingView (do let p ← getPeer pid; setPeer pid (f p)) := by
  intro s
  apply hoare_bind _ _ (routing_getPeer (fun view => view = s) pid)
  intro p
  apply hoare_consequence (routing_setPeer (fun view => view = s) pid (f p))
  · intro w h
    simpa only [hl] using h
  · exact fun _ _ h => h

theorem setPeerEndpoint_routing (pid : PeerId) (e : Endpoint) : SameView routingView (setPeerEndpoint pid e) := by
  routing_handshake_source [setPeerEndpoint, endpointEq] using [dstCacheReset_routing]

theorem armTimer_routing (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView routingView (armTimer pid timer delay jc) := by
  have wheel (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameView routingView (placeOnWheel pid t expires clk unit) := by
    routing_handshake_source [placeOnWheel] using []

  have ambient {α : Type} (a : AmbientM α) : SameView routingView (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => routingView w = initial)
  have read : SameView routingView (get : WG.M WGWorld) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
    rfl
  have dev : SameView routingView getDev := by
    exact routing_kernel _ getDev_sameWGStore
  have stopped {α : Type} (e : Stop) : SameView routingView (throw e : WG.M α) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w ambient x v ambient' hr
    cases hr
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
  routing_handshake_source [modPeerTimerGuard] using []

theorem modPeerTimer_routing (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView routingView (modPeerTimer site pid timer delay) := by
  have clock : SameView routingView (callerJiffies site) :=
    (callerJiffies_sameWGWorld site).factor routingView
  have arm := fun p t d jc => armTimer_routing p t d jc
  routing_handshake_source [modPeerTimer] using [modPeerTimerGuard_routing, clock, arm]

theorem timersTraversal_routing (pid : PeerId) : SameView routingView (timersTraversal pid) := by
  routing_handshake_source [timersTraversal, Functor.discard] using [modPeerTimer_routing]

theorem timersAnyAuthenticatedPacketSent_routing (pid : PeerId) :
    SameView routingView (timersAnyAuthenticatedPacketSent pid) := delTimer_routing pid .sendKeepalive

theorem timersHandshakeInitiated_routing (pid : PeerId) :
    SameView routingView (timersHandshakeInitiated pid) := by
  have clock : SameView routingView (callerJiffies .timerJiffiesHandshakeInitiated) :=
    (callerJiffies_sameWGWorld .timerJiffiesHandshakeInitiated).factor routingView
  have jitter : SameView routingView (jitterBelowRekeyTimeout .retransmitJitter) :=
    (jitterBelowRekeyTimeout_sameWGWorld .retransmitJitter).factor routingView
  have arm := fun p t d jc => armTimer_routing p t d jc
  routing_handshake_source [timersHandshakeInitiated] using [clock, jitter, modPeerTimerGuard_routing, arm]

theorem createInitiation_routing (pid : PeerId) : SameView routingView (createInitiation pid) := by
  have pub := fun k => show SameView routingView _ from
    (generatePublic_sameWGWorld k).factor routingView
  have eph := fun b e ck h => show SameView routingView _ from
    (messageEphemeral_sameWGWorld b e ck h).factor routingView
  have dh := fun b ck p q => show SameView routingView _ from
    (mixDh_sameWGWorld b ck p q).factor routingView
  have pre := fun ck p => show SameView routingView _ from
    (mixPrecomputedDh_sameWGWorld ck p).factor routingView
  routing_handshake_source [createInitiation,
    _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain] using [pub, eph, dh, pre]

theorem addMacToPacket_routing (pid : PeerId) (msg : List UInt8) :
    SameView routingView (addMacToPacket pid msg) := by
  have expired := fun d b n f => show SameView routingView _ from
    (branchExpired_sameWGWorld d b n f).factor routingView
  routing_handshake_source [addMacToPacket] using [expired]

theorem sendBufferToPeer_routing (pid : PeerId) (bytes : List UInt8) :
    SameView routingView (sendBufferToPeer pid bytes) := by
  routing_handshake_source [sendBufferToPeer] using [send4_routing, send6_routing]

theorem sendHandshakeInitiation_routing (pid : PeerId) : SameView routingView (sendHandshakeInitiation pid) := by
  have expired := fun date => show SameView routingView _ from
    (branchExpired_sameWGWorld .initRateLimited date REKEY_TIMEOUT (!·)).factor routingView
  routing_handshake_source [sendHandshakeInitiation] using [expired, createInitiation_routing,
    addMacToPacket_routing, timersTraversal_routing, timersAnyAuthenticatedPacketSent_routing,
    sendBufferToPeer_routing, timersHandshakeInitiated_routing]

theorem handshakeZero_routing (pid : PeerId) : SameView routingView (handshakeZero pid) := by
  routing_handshake_source [handshakeZero] using []

theorem keypairsClear_routing (pid : PeerId) : SameView routingView (keypairsClear pid) := by
  routing_handshake_source [keypairsClear,
    _private.Leanux.WG.Keypair.«0».Leanux.WG.modifyPeer] using [keypairPut_routing]

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
  intro s
  have main : Preserves (fun w => RetainsRouting s (routingView w)) (handshakeSendWorker pid) := by
    unfold handshakeSendWorker
    exact preserves_bind ((sendHandshakeInitiation_routing pid).wp (RetainsRouting s))
      (fun _ => RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s)
  apply hoare_consequence main
  · intro w h
    change routingView w = s at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem queuedExpiredZeroKeyMaterial_routing (pid : PeerId) : RetainsRoutingCall (queuedExpiredZeroKeyMaterial pid) := by
  intro s
  have main : Preserves (fun w => RetainsRouting s (routingView w)) (queuedExpiredZeroKeyMaterial pid) := by
    unfold queuedExpiredZeroKeyMaterial
    exact preserves_bind ((handshakeClear_routing pid).wp (RetainsRouting s)) (fun _ =>
      preserves_bind ((keypairsClear_routing pid).wp (RetainsRouting s))
        (fun _ => RetainsRoutingCall.wp (peerPut_retainsRouting (some pid)) s))
  apply hoare_consequence main
  · intro w h
    change routingView w = s at h
    rw [h]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.AllowedIps
