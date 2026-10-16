import Lean
import Leanux.Proofs.WG.Queues.RxQueuePrimitives
import Leanux.Proofs.Framing.WGTime
import Leanux.Proofs.WG.Keypairs.Frames.WGBase

set_option maxHeartbeats 800000
set_option pp.structureInstances false

/-! Original endpoint and timer maintenance frames. Hidden-input validation
and failures remain in the original operations; no time or ownership premise
is added to the successful-endpoint queue contracts. -/
namespace Leanux.Proofs.WG.Queues
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do

/-- Factor an actual generated continuation, retaining the current SameView
predicate and state stack. The resulting proof is checked by the kernel. -/
elab "rxqueue_join_let" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameView do Lean.throwError "not SameView"
  let .app property action := target | Lean.throwError "missing action"
  let .letE name ty value body _ := action.consumeMData | Lean.throwError "not a let"
  unless name.toString.startsWith "__do_jp" do Lean.throwError "not a join continuation"
  let contract ← Lean.Meta.forallTelescope ty fun args _ =>
    Lean.Meta.mkForallFVars args (.app property (Lean.mkAppN value args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar contract
  let (continuation, next) ← Lean.Meta.withLocalDeclD name ty fun f => do
    let contract ← Lean.Meta.forallTelescope ty fun args _ =>
      Lean.Meta.mkForallFVars args (.app property (Lean.mkAppN f args))
    Lean.Meta.withLocalDeclD `rxqueue_join contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (.app property (body.instantiate1 f))
      let proof ← Lean.Meta.mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (Lean.mkApp2 continuation value valueProof)
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "rxqueue_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``SameView do Lean.throwError "not SameView"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do Lean.throwError "not a local continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `rxqueue_join then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no continuation contract"

theorem dstCacheReset_rxQueues (pid : PeerId) : SameView rxQueues (dstCacheReset pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) :=
    hoare_liftAmbient a (fun w => rxQueues w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, dstCacheReset, getAmbient, hiddenJiffies, hg, hs, ambient]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem setPeerEndpoint_rxQueues (pid : PeerId) (e : Endpoint) : SameView rxQueues (setPeerEndpoint pid e) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have hn := (requireNotPending_rxQueues pid "changing the endpoint").wp (fun t => t = s)
  have hc := (dstCacheReset_rxQueues pid).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) :=
    hoare_liftAmbient a (fun w => rxQueues w = s)
  unfold Hoare at ambient
  have he (old : Option Endpoint) :
      ⦃fun w => ⌜rxQueues w = s⌝⦄ endpointEq e old ⦃⇓? _ w => ⌜rxQueues w = s⌝⦄ := by
    mvcgen [-Std.Do.Spec.monadLift_StateT, endpointEq, WG.andM, branch, ambient]
  mvcgen [-Std.Do.Spec.monadLift_StateT, setPeerEndpoint, he, hg, hs, hn, hc, branch, ambient]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem armTimer_rxQueues (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView rxQueues (armTimer pid timer delay jc) := by
  have wheel (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameView rxQueues (placeOnWheel pid t expires clk unit) := by
    apply SameView.of_wp
    intro s
    have hg : ⦃fun w => ⌜rxQueues w = s⌝⦄ getPeer pid
        ⦃⇓? p w => ⌜rxQueues w = s ∧ CurrentRx s pid p⌝⦄ :=
      hoare_consequence (getPeer_rx_spec (fun q => q = s) pid) (fun _ h => h)
        (fun p w h => ⟨h.1, h.1 ▸ h.2⟩)
    have hs := fun p => setPeer_rx_spec (fun q => q = s) pid p
    have ambient {α : Type} (a : AmbientM α) :
        Hoare (MonadLift.monadLift a : WG.M α) (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) :=
      hoare_liftAmbient a (fun w => rxQueues w = s)
    have current (w : WGWorld) (p : Peer)
        (h : rxQueues w = s ∧ CurrentRx s pid p) : CurrentRx (rxQueues w) pid p :=
      h.1.symm ▸ h.2
    unfold Hoare at ambient
    mvcgen [-Std.Do.Spec.monadLift_StateT, placeOnWheel, hg, hs, ambient,
      hidden, peekHiddenSite, invariant]
    all_goals have timer_stamp (p : Peer) (e : Option UInt64) :
        (p.setTimer t e).internalId = p.internalId := by cases t <;> rfl
    all_goals have timer_queue (p : Peer) (e : Option UInt64) :
        (p.setTimer t e).rxQueue = p.rxQueue := by cases t <;> rfl
    all_goals have wheel_stamp (p : Peer) (e : Option WheelEntry) :
        (p.setWheel t e).internalId = p.internalId := by cases t <;> rfl
    all_goals have wheel_queue (p : Peer) (e : Option WheelEntry) :
        (p.setWheel t e).rxQueue = p.rxQueue := by cases t <;> rfl
    all_goals try simp only [CurrentRx, timer_stamp, timer_queue, wheel_stamp, wheel_queue]
    all_goals first
      | assumption
      | exact And.left (by assumption)
      | (constructor
         · first | assumption | exact And.left (by assumption)
         · apply current <;> first
             | assumption
             | exact And.left (by assumption)
             | exact And.right (by assumption))

  have ambient {α : Type} (a : AmbientM α) : SameView rxQueues (monadLift a : WG.M α) :=
    fun initial => hoare_liftAmbient a (fun w => rxQueues w = initial)
  have read : SameView rxQueues (get : WG.M WGWorld) := by
    apply SameView.of_wp; intro initial; mvcgen
  have dev : SameView rxQueues getDev := by
    apply SameView.of_wp; intro initial; mvcgen [getDev, invariant, AmbientM.invariant]
  have stopped {α : Type} (e : Stop) : SameView rxQueues (throw e : WG.M α) := by
    apply SameView.of_wp; intro initial; mvcgen
  have edit (f : WGWorld → WGWorld) (hf : ∀ w, rxQueues (f w) = rxQueues w) :
      SameView rxQueues (modify f : WG.M Unit) := by
    intro initial
    apply hoare_modify
    intro w hw
    exact (hf w).trans hw
  unfold armTimer
  simp (config := { zeta := false }) only [getAmbient, hidden, invariant, unsupported, liftM]
  repeat' first
    | rxqueue_join_let
    | rxqueue_join_use
    | (snapshot_head placeOnWheel; exact wheel _ _ _ _)
    | (snapshot_head getDev; exact dev)
    | (snapshot_head getPeer; exact getPeer_rxQueues _)
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

theorem delTimer_rxQueues (pid : PeerId) (timer : PeerTimer) : SameView rxQueues (delTimer pid timer) :=
  modifyPeer_rxQueues pid (fun p => (p.setTimer timer none).setWheel timer none)
    (fun p => by cases timer <;> rfl) (fun p => by cases timer <;> rfl)

theorem modPeerTimerGuard_rxQueues (pid : PeerId) : SameView rxQueues (modPeerTimerGuard pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_rxQueues pid).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) :=
    hoare_liftAmbient a (fun w => rxQueues w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, modPeerTimerGuard, getDev, hg, WG.andM, branch, invariant, AmbientM.invariant]

theorem modPeerTimer_rxQueues (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView rxQueues (modPeerTimer site pid timer delay) := by
  apply SameView.of_wp
  intro s
  have hg := (modPeerTimerGuard_rxQueues pid).wp (fun t => t = s)
  have ha := fun jc => (armTimer_rxQueues pid timer delay jc).wp (fun t => t = s)
  have hc := (callerJiffies_sameWGWorld site).wp (fun w => rxQueues w = s)
  mvcgen [modPeerTimer, hg, ha, hc]

theorem timersHandshakeComplete_rxQueues (pid : PeerId) (site : HiddenSite) :
    SameView rxQueues (timersHandshakeComplete pid site) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have hd := (delTimer_rxQueues pid .retransmitHandshake).wp (fun t => t = s)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) :=
    hoare_liftAmbient a (fun w => rxQueues w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, timersHandshakeComplete, hg, hs, hd, hidden, ambient]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem timersAnyAuthenticatedPacketReceived_rxQueues (pid : PeerId) :
    SameView rxQueues (timersAnyAuthenticatedPacketReceived pid) := delTimer_rxQueues pid .newHandshake

theorem timersDataReceived_rxQueues (pid : PeerId) : SameView rxQueues (timersDataReceived pid) := by
  apply SameView.of_wp
  intro s
  have hg := getPeer_rx_spec (fun t => t = s) pid
  have hs := fun p => setPeer_rx_spec (fun t => t = s) pid p
  have ht := (modPeerTimer_rxQueues .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).wp (fun t => t = s)
  have hd := discard_view_spec rxQueues (fun t => t = s) _ ht
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) :=
    hoare_liftAmbient a (fun w => rxQueues w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, timersDataReceived, hg, hs, ht, hd, getDev, branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals unfold rxQueues at *; simp_all [CurrentRx]

theorem timersTraversal_rxQueues (pid : PeerId) : SameView rxQueues (timersTraversal pid) := by
  apply SameView.of_wp
  intro s
  have hg := (getPeer_rxQueues pid).wp (fun t => t = s)
  have ht := fun delay => (modPeerTimer_rxQueues .timerJiffiesTraversal pid .persistentKeepalive delay).wp (fun t => t = s)
  have hd := fun delay => discard_view_spec rxQueues (fun t => t = s) _ (ht delay)
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => rxQueues w = s) (fun _ w => rxQueues w = s) :=
    hoare_liftAmbient a (fun w => rxQueues w = s)
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, timersTraversal, hg, ht, hd, branchCmp]

/-- Queueing a handshake can release the extra peer reference. Retention
allows the original release semantics instead of requiring ownership. -/
theorem sendQueuedHandshakeInitiation_rxQueues (pid : PeerId) (retry : Bool) :
    RetainsRx (sendQueuedHandshakeInitiation pid retry) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hg := getPeer_rx_spec P pid
  have hs := fun p => setPeer_rx_spec P pid p
  have hn := (requireNotPending_rxQueues pid "queueing a handshake").wp P
  have hc := fun date => (branchExpired_sameWGWorld .queuedNotExpired date REKEY_TIMEOUT (!·)).wp (fun w => P (rxQueues w))
  have hget := (peerGet_rxQueues pid).wp P
  have hput := RetainsRx.wp (peerPut_rxQueues (some pid)) s
  have hqueue := (modifyDev_rxQueues (fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (fun _ => rfl) (fun _ => rfl)).wp P
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => P (rxQueues w)) (fun _ w => P (rxQueues w)) :=
    hoare_liftAmbient a (fun w => P (rxQueues w))
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, sendQueuedHandshakeInitiation, hg, hs, hn, hc, hget, hput, hqueue, branch, peekQueuedUnit, recordQueued, ambient]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx])
  all_goals subst s
  all_goals exact rx_retained_refl _

theorem keepKeyFreshRx_rxQueues (pid : PeerId) : RetainsRx (keepKeyFreshRx pid) := by
  apply ProjectedAction.of_wp
  intro s
  let P := ResidentsRetained s
  have hg := getPeer_rx_spec P pid
  have hs := fun p => setPeer_rx_spec P pid p
  have hk := fun id => (getKeypair_rxQueues id).wp P
  have ht := fun date delay => (branchExpired_sameWGWorld .rxFreshExpired date delay).wp (fun w => P (rxQueues w))
  have hq := RetainsRx.wp (sendQueuedHandshakeInitiation_rxQueues pid false) s
  have ambient {α : Type} (a : AmbientM α) :
      Hoare (MonadLift.monadLift a : WG.M α) (fun w => P (rxQueues w)) (fun _ w => P (rxQueues w)) :=
    hoare_liftAmbient a (fun w => P (rxQueues w))
  unfold Hoare at ambient
  mvcgen [-Std.Do.Spec.monadLift_StateT, ambient, keepKeyFreshRx, hg, hs, hk, ht, hq, WG.andM, branch, invariant, AmbientM.invariant]
  all_goals try dsimp +zetaDelta only [P] at *
  all_goals try (unfold rxQueues at *; simp_all [CurrentRx])
  all_goals subst s
  all_goals exact rx_retained_refl _

end Leanux.Proofs.WG.Queues
