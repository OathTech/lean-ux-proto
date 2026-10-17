import Leanux.Proofs.WG.Origins.IndexMaterial
import Leanux.Proofs.WG.Queues.RxRingHandshake
import Leanux.Proofs.Framing.WGCookie
import Leanux.Proofs.Framing.WGConfiguration
import Leanux.Proofs.Framing.WGDeviceLifecycle
import Leanux.Proofs.WG.Lifetimes.CookieAccess

/-! Concrete normal-return frames for the complete receiving-material view.
Peer and packet writes retain that view; key writes use actual resident records.
These contracts neither establish initial support nor retain erased objects. -/
namespace Leanux.Proofs.WG.Origins.Retaining
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged
open Leanux.Proofs.WG.Lifetimes Leanux.Proofs.WG.Queues Std.Do
set_option pp.structureInstances false

/-- Actual-state relational contracts retain arbitrary product callbacks. -/
abbrev ProjectedRetainsCall {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] (project : S → WGWorld) (a : StateT S m α) :=
  ProjectedAction (fun s => view (project s)) RetainsView a

abbrev RetainsCall (a : WG.M α) := ProjectedRetainsCall id a

theorem ProjectedRetainsCall.wp {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : ProjectedRetainsCall project a) (s : View) :
    ⦃fun w => ⌜RetainsView s (view (project w))⌝⦄ a
    ⦃⇓? _ w => ⌜RetainsView s (view (project w))⌝⦄ :=
  ProjectedAction.wp h (RetainsView s) (fun _ _ hr hs => hs.trans hr)

theorem RetainsCall.wp (h : RetainsCall a) (s : View) :
    ⦃fun w => ⌜RetainsView s (view w)⌝⦄ a
    ⦃⇓? _ w => ⌜RetainsView s (view w)⌝⦄ := ProjectedRetainsCall.wp h s

theorem of_view {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : SameView (fun s => view (project s)) a) : ProjectedRetainsCall project a :=
  retains_of_sameView h

theorem ProjectedRetainsCall.of_same {S α : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld} {a : StateT S m α}
    (h : SameView (fun s => view (project s)) a) : ProjectedRetainsCall project a := of_view h

/-- Stops have no returned state. The normal endpoint bridge also covers
arbitrary product actions via the actual World.wg projection. -/
theorem ProjectedRetainsCall.support {S α : Type} {project : S → WGWorld}
    {a : StateT S (Except Stop) α} {w v : S} {result : α} (ha : ProjectedRetainsCall project a)
    (hi : Inv history (project w)) (hr : a.run w = .ok (result,v)) :
    Inv history (project v) :=
  hi.retain ((ProjectedAction.iff_run _ _ _).mp ha w result v hr)

theorem RetainsCall.support (ha : RetainsCall a) (hi : Inv history w)
    (hr : (a.run w).run ambient = .ok ((result,v),ambient')) : Inv history v :=
  hi.retain ((ProjectedAction.iff_run_ambient view RetainsView a).mp ha
    w ambient result v ambient' hr)

def materialState (d : Device) : Nat × (KeypairId → Option Keypair) :=
  (d.ifindex, fun id => d.keypairs[id]?)

theorem material_getPeer (P : View → Prop) (pid : PeerId) :
    ⦃fun w => ⌜P (view w)⌝⦄ getPeer pid ⦃⇓? _ w => ⌜P (view w)⌝⦄ := (getPeer_view pid).wp P

theorem material_setPeer (P : View → Prop) (pid : PeerId) (p : Peer) :
    ⦃fun w => ⌜P (view w)⌝⦄ setPeer pid p ⦃⇓? _ w => ⌜P (view w)⌝⦄ := (setPeer_view pid p).wp P

theorem modifyDev_material (f : Device → Device)
    (hf : ∀ d, ((f d).ifindex,(f d).keypairs) = (d.ifindex,d.keypairs)) :
    SameView view (modifyDev f) := by
  apply SameView.of_wp
  intro s
  exact modifyDev_spec (fun t => t = s) f (fun d => congrArg Prod.fst (hf d))
    (fun d => congrArg Prod.snd (hf d))

theorem getPeer_material (pid : PeerId) : SameView view (getPeer pid) := getPeer_view pid

theorem getKeypair_material (id : KeypairId) : SameView view (getKeypair id) := by
  intro initial
  exact hoare_consequence (getKeypair_spec (fun s => s = initial) id)
    (fun _ h => h) (fun _ _ h => h.1)

theorem requireNotPending_material (pid : PeerId) (why : String) :
    SameView view (requireNotPending pid why) := SameView.pure view ()

theorem ownerDeref_material (o : IndexOwner) : SameView view o.peerDeref := fun initial => indexOwner_peerDeref_preserves o (fun w => view w = initial)

theorem ownerWord_material (o : IndexOwner) : SameView view o.peerWord := fun initial => indexOwner_peerWord_preserves o (fun w => view w = initial)

open Lean Meta Elab Tactic

/-- Goal selection and continuation factoring only construct ordinary Hoare
proofs; all branches remain kernel obligations. -/
elab "material_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let i := args.size - 3
  let action := args[i]!.consumeMData
  let .letE name ty value body _ := action | throwError "not a let"
  unless name.toString.startsWith "__do_jp" do throwError "not a shared continuation"
  let property := fun a => mkAppN target.getAppFn (args.set! i a)
  let contract ← forallTelescope ty fun xs _ => mkForallFVars xs (property (mkAppN value xs))
  let valueProof ← mkFreshExprSyntheticOpaqueMVar contract
  let (proof, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun xs _ => mkForallFVars xs (property (mkAppN f xs))
    withLocalDeclD `material_continuation contract fun hf => do
      let next ← mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 f))
      pure (← mkLambdaFVars #[f,hf] next, next.mvarId!)
  goal.assign (mkApp2 proof value valueProof)
  replaceMainGoal [valueProof.mvarId!,next]

elab "material_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let action := args[args.size-3]!.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `material_continuation then
      let proof := mkAppN decl.toExpr action.getAppArgs
      if ← withReducible (isDefEq (← inferType proof) target) then
        goal.assign proof
        replaceMainGoal []
        return
  throwError "no continuation contract"

macro "material_intro" : tactic => `(tactic| run_tac do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do Lean.throwError "not a function argument"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro x)))

elab "material_component" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let action := args[args.size-3]!.consumeMData
  let .const name _ := action.getAppFn | throwError "not a component lift"
  unless [``monadLift, ``MonadLiftT.monadLift, ``MonadLift.monadLift,
      ``StateT.lift, ``liftIndex, ``liftRouting].contains name do
    throwError "not a component lift"
  let source := action.getAppArgs.back!
  let pre := args[args.size-2]!
  for lemma in [``hoare_liftAmbient, ``hoare_liftIndex, ``hoare_liftRouting] do
    let saved ← saveState
    try
      let proof ← mkAppM lemma #[source,pre]
      replaceMainGoal (← goal.apply proof)
      if lemma == ``hoare_liftIndex then
        evalTactic (← `(tactic| (intro w d table hi hd; simpa only [view,hd,Option.map_some] using hi)))
      else if lemma == ``hoare_liftRouting then
        evalTactic (← `(tactic| exact fun _ _ hi => hi))
      return
    catch _ => saved.restore
  throwError "no applicable canonical adapter"

private theorem material_ite {α : Type} (c : Prop) [Decidable c]
    (a b : WG.M α) (P : WGWorld → Prop)
    (ha : Hoare a P (fun _ => P)) (hb : Hoare b P (fun _ => P)) :
    Hoare (if c then a else b) P (fun _ => P) := by
  by_cases h : c
  · simpa only [ite_eq_left h] using ha
  · simpa only [ite_eq_right h] using hb

private def materialHeadBZ : Nat → Expr → Expr
  | 0, e => e
  | n+1, e =>
    let e := e.consumeMData
    match e with
    | .letE name _ v b _ =>
      if name.toString.startsWith "__do_jp" then e else materialHeadBZ n (b.instantiate1 v)
    | _ =>
      match e.getAppFn.consumeMData with
      | .letE name _ v b _ =>
        if name.toString.startsWith "__do_jp" then e
        else materialHeadBZ n (mkAppN (b.instantiate1 v) e.getAppArgs)
      | .lam .. =>
        let e' := e.headBeta
        if Expr.equal e e' then e else materialHeadBZ n e'
      | _ => e

elab "material_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let i := args.size-3
  let action := args[i]!
  let reduced := materialHeadBZ 64 action
  if Expr.equal action reduced then throwError "head unchanged"
  replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! i reduced))]

elab "material_match" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless (target.isAppOf ``Hoare || target.isAppOf ``Triple) && args.size ≥ 3 do
    throwError "not an endpoint contract"
  let action := args[args.size-3]!.consumeMData
  let some _ ← matchMatcherApp? action | throwError "not an action matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch goal action)

macro "material_basic" P:term : tactic => `(tactic|
  first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head getPeer; exact material_getPeer $P _)
    | (index_material_head setPeer; exact material_setPeer $P _ _)
    | (index_material_head getKeypair; exact (getKeypair_material _).wp $P)
    | (index_material_head IndexOwner.peerWord; exact (ownerWord_material _).wp $P)
    | (index_material_head IndexOwner.peerDeref; exact (ownerDeref_material _).wp $P)
    | (index_material_head requireNotPending; exact preserves_pure ())
    | (index_material_head modifyDev; exact modifyDev_spec $P _ (fun _ => rfl) (fun _ => rfl))
    | (index_material_head getDev; exact (sameView_of_sameWG (project := id) getDev_sameWGStore).wp $P)
    | (first | index_material_head get | index_material_head MonadStateOf.get
       exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
    | (index_material_head modify; apply hoare_modify; intro w hw; exact hw)
    | material_component
    | (first | index_material_head throw | index_material_head MonadExceptOf.throw
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w ambient x v ambient' hi hr
       cases hr)
    | (index_material_head ForIn.forIn; apply list_view_spec view $P; intro x b)
    | (index_material_head discard; apply discard_view_spec view $P)
    | material_intro
    | (index_material_head ite; apply material_ite)
    | material_reduce
    | material_match
    | contradiction)

macro "material_lower" : tactic => `(tactic|
  simp (config := {zeta := false}) only [branch,branchCmp,branchCmpExcluded,
    invariant,unsupported,hidden,hiddenU64,hiddenClock64,hiddenJiffies,hiddenAlloc,
    getAmbient,modifyAmbient,getRouting,liftM])

macro "material_known" P:term : tactic => `(tactic|
  first
    | (index_material_head callerJiffies; exact (callerJiffies_sameWGWorld _).wp (fun w => $P (view w)))
    | (index_material_head jitterBelowRekeyTimeout; exact (jitterBelowRekeyTimeout_sameWGWorld _).wp (fun w => $P (view w)))
    | (index_material_head branchExpired; exact (branchExpired_sameWGWorld _ _ _ _).wp (fun w => $P (view w)))
    | (index_material_head generatePublic; exact (generatePublic_sameWGWorld _).wp (fun w => $P (view w)))
    | (index_material_head messageEphemeral; exact (messageEphemeral_sameWGWorld _ _ _ _).wp (fun w => $P (view w)))
    | (index_material_head mixDh; exact (mixDh_sameWGWorld _ _ _ _).wp (fun w => $P (view w)))
    | (index_material_head mixPrecomputedDh; exact (mixPrecomputedDh_sameWGWorld _ _).wp (fun w => $P (view w)))
    | (index_material_head messageDecrypt; exact (messageDecrypt_sameWGWorld _ _ _).wp (fun w => $P (view w)))
    | (index_material_head kdf; exact (Framing.kdf_sameWGWorld _ _ _ _).wp (fun w => $P (view w)))
    | (index_material_head kdfOut; exact (Framing.kdfOut_sameWGWorld _ _).wp (fun w => $P (view w))))

theorem peerGet_material (pid : PeerId) : SameView view (peerGet pid) := by
  intro initial
  unfold peerGet refcountInc
  material_lower
  repeat' material_basic (fun t => t = initial)

theorem peerPut_material (pid : Option PeerId) : SameView view (peerPut pid) := by
  intro initial
  unfold peerPut retirePeerUnits refcountDecAndTest
  material_lower
  repeat' material_basic (fun t => t = initial)

theorem keypairGet_material (kp : Option KeypairId) : RetainsCall (keypairGet kp) := by
  apply ProjectedAction.of_wp
  intro initial
  exact hoare_consequence (keypairGet_spec (RetainsView initial) (fun _ _ hr hi => hi.trans hr) kp)
    (fun _ h => by dsimp only [id] at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)

theorem keypairPut_material (kp : Option KeypairId) (now : Bool) : RetainsCall (keypairPut kp now) := by
  apply ProjectedAction.of_wp
  intro initial
  exact hoare_consequence (keypairPut_spec (RetainsView initial) (fun _ _ hr hi => hi.trans hr) kp now)
    (fun _ h => by dsimp only [id] at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)

theorem keypairCreate_material (word : Option PeerId) : RetainsCall (keypairCreate word) := by
  apply (ProjectedAction.iff_run_ambient view RetainsView _).mpr
  intro w ambient x v ambient' hr
  exact create_retains word w v x ambient ambient' hr

theorem pubkeyLookup_material (key : Key) : SameView view (pubkeyLookup key) := by
  have borrow (peer : Option PeerId) : SameView view (peerGetMaybeZero peer) := by
    intro initial
    unfold peerGetMaybeZero refcountIncNotZero
    material_lower
    repeat' material_basic (fun t => t = initial)
  intro initial
  unfold pubkeyLookup
  material_lower
  repeat' first
    | (index_material_head peerGetMaybeZero; exact (borrow _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem dstCacheReset_material (pid : PeerId) : SameView view (dstCacheReset pid) := by
  intro initial
  unfold dstCacheReset
  material_lower
  repeat' material_basic (fun t => t = initial)

theorem dstCacheGet_material (pid : PeerId) (gen : Nat) : SameView view (dstCacheGet pid gen) := by
  intro initial
  unfold dstCacheGet
  material_lower
  repeat' material_basic (fun t => t = initial)

theorem dstCacheSet_material (pid : PeerId) (src gen dev : Nat) : SameView view (dstCacheSet pid src gen dev) := by
  intro initial
  unfold dstCacheSet
  material_lower
  repeat' material_basic (fun t => t = initial)

theorem tunnelXmit_material (e : Endpoint) (bytes : List UInt8) (ds : Nat) (r : Route) (exactRx : Bool) :
    SameView view ((pinned_const _private.Leanux.WG.Socket.«0».Leanux.WG.tunnelXmit) e bytes ds r exactRx) := by
  rw [tunnelXmitSource_eq]
  intro initial
  have hl := fun sites force => (sameView_of_sameWG (project := id)
    (loopbackSend_kernel sites force)).wp (fun t => t = initial)
  have hp := fun family => (sameView_of_sameWG (project := id)
    (socketPort_sameStore family)).wp (fun t => t = initial)
  unfold tunnelXmitSource
  simp (config := {zeta := false}) only [skipCut]
  material_lower
  repeat' first
    | (index_material_head loopbackSend; exact hl _ _)
    | (index_material_head socketPort; exact hp _)
    | material_basic (fun t => t = initial)

theorem send4ClearSrc_material cache : SameView view (send4ClearSrcSource cache) := by
  intro initial
  unfold send4ClearSrcSource
  material_lower
  repeat' first
    | material_basic (fun t => t = initial)

theorem send4Finish_material e bytes ds exactRx route : SameView view (send4FinishSource e bytes ds exactRx route) := by
  intro initial
  unfold send4FinishSource
  material_lower
  repeat' first
    | (index_material_head tunnelXmit; exact (tunnelXmit_material _ _ _ _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem send4RouteDone_material e cache bytes ds exactRx gen fallback rt :
    SameView view (send4RouteDoneSource e cache bytes ds exactRx gen fallback rt) := by
  intro initial
  unfold send4RouteDoneSource
  material_lower
  repeat' first
    | (index_material_head dstCacheSet; exact (dstCacheSet_material _ _ _ _).wp (fun t => t = initial))
    | (index_material_head send4FinishSource; exact (send4Finish_material _ _ _ _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem send4Retry_material e cache bytes ds exactRx gen fallback srcIf rt :
    SameView view (send4RetrySource e cache bytes ds exactRx gen fallback srcIf rt) := by
  intro initial
  unfold send4RetrySource
  material_lower
  repeat' first
    | (index_material_head send4ClearSrcSource; exact (send4ClearSrc_material _).wp (fun t => t = initial))
    | (index_material_head dstCacheReset; exact (dstCacheReset_material _).wp (fun t => t = initial))
    | (index_material_head send4RouteDoneSource; exact (send4RouteDone_material _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem send4Miss_material e cache bytes ds exactRx gen fallback saddr srcIf :
    SameView view (send4MissSource e cache bytes ds exactRx gen fallback saddr srcIf) := by
  intro initial
  unfold send4MissSource
  material_lower
  repeat' first
    | (index_material_head send4ClearSrcSource; exact (send4ClearSrc_material _).wp (fun t => t = initial))
    | (index_material_head dstCacheReset; exact (dstCacheReset_material _).wp (fun t => t = initial))
    | (index_material_head send4RetrySource; exact (send4Retry_material _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem send4AfterCache_material e cache bytes ds exactRx gen saddr srcIf route :
    SameView view (send4AfterCacheSource e cache bytes ds exactRx gen saddr srcIf route) := by
  intro initial
  unfold send4AfterCacheSource
  material_lower
  repeat' first
    | (index_material_head send4MissSource; exact (send4Miss_material _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | (index_material_head send4FinishSource; exact (send4Finish_material _ _ _ _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem send4_material e cache bytes ds exactRx : SameView view (send4 e cache bytes ds exactRx) := by
  rw [← send4Source_eq]
  intro initial
  unfold send4Source
  material_lower
  repeat' first
    | (index_material_head dstCacheGet; exact (dstCacheGet_material _ _).wp (fun t => t = initial))
    | (index_material_head send4AfterCacheSource; exact (send4AfterCache_material _ _ _ _ _ _ _ _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem send6_material e cache bytes ds exactRx : SameView view (send6 e cache bytes ds exactRx) := by
  intro initial
  unfold send6
  material_lower
  repeat' first
    | (index_material_head dstCacheGet; exact (dstCacheGet_material _ _).wp (fun t => t = initial))
    | (index_material_head dstCacheReset; exact (dstCacheReset_material _).wp (fun t => t = initial))
    | (index_material_head dstCacheSet; exact (dstCacheSet_material _ _ _ _).wp (fun t => t = initial))
    | (index_material_head tunnelXmit; exact (tunnelXmit_material _ _ _ _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem modifyPeer_material (pid : PeerId) (f : Peer → Peer)
    :
    SameView view (do let p ← getPeer pid; setPeer pid (f p)) := by
  intro initial
  repeat' material_basic (fun t => t = initial)

theorem setPeerEndpoint_material (pid : PeerId) (e : Endpoint) : SameView view (setPeerEndpoint pid e) := by
  intro initial
  unfold setPeerEndpoint endpointEq WG.andM
  material_lower
  repeat' first
    | (index_material_head dstCacheReset; exact (dstCacheReset_material _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem armTimer_material (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64 := none) :
    SameView view (armTimer pid timer delay jc) := by
  have wheel (t : PeerTimer) (expires clk : UInt64) (unit : Option Nat) :
      SameView view (placeOnWheel pid t expires clk unit) := by
    intro initial
    unfold placeOnWheel
    simp (config := {zeta := false}) only [peekHiddenSite]
    material_lower
    repeat' material_basic (fun t => t = initial)
  intro initial
  unfold armTimer
  material_lower
  repeat' first
    | (index_material_head placeOnWheel; exact (wheel _ _ _ _).wp (fun t => t = initial))
    | material_basic (fun t => t = initial)

theorem delTimer_material (pid : PeerId) (timer : PeerTimer) : SameView view (delTimer pid timer) := modifyPeer_material pid (fun p => (p.setTimer timer none).setWheel timer none)

theorem modPeerTimerGuard_material (pid : PeerId) : SameView view (modPeerTimerGuard pid) := by
  intro initial
  unfold modPeerTimerGuard WG.andM
  material_lower
  repeat' material_basic (fun t => t = initial)

theorem modPeerTimer_material (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    SameView view (modPeerTimer site pid timer delay) := by
  intro initial
  unfold modPeerTimer
  material_lower
  repeat' first
    | (index_material_head modPeerTimerGuard; exact (modPeerTimerGuard_material _).wp (fun t => t = initial))
    | (index_material_head armTimer; exact (armTimer_material _ _ _ _).wp (fun t => t = initial))
    | material_known (fun t => t = initial)
    | material_basic (fun t => t = initial)

theorem timersTraversal_material (pid : PeerId) : SameView view (timersTraversal pid) := by
  intro initial
  unfold timersTraversal
  material_lower
  repeat' first
    | (index_material_head modPeerTimer; exact (modPeerTimer_material _ _ _ _).wp (fun t => t = initial))
    | material_known (fun t => t = initial)
    | material_basic (fun t => t = initial)

theorem timersAnyAuthenticatedPacketSent_material (pid : PeerId) :
    SameView view (timersAnyAuthenticatedPacketSent pid) := delTimer_material pid .sendKeepalive

theorem timersHandshakeInitiated_material (pid : PeerId) :
    SameView view (timersHandshakeInitiated pid) := by
  intro initial
  unfold timersHandshakeInitiated
  material_lower
  repeat' first
    | (index_material_head modPeerTimerGuard; exact (modPeerTimerGuard_material _).wp (fun t => t = initial))
    | (index_material_head armTimer; exact (armTimer_material _ _ _ _).wp (fun t => t = initial))
    | material_known (fun t => t = initial)
    | material_basic (fun t => t = initial)

theorem createInitiation_material (pid : PeerId) : SameView view (createInitiation pid) := by
  intro initial
  unfold createInitiation
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  material_lower
  repeat' first
    | material_known (fun t => t = initial)
    | material_basic (fun t => t = initial)

theorem addMacToPacket_material (pid : PeerId) (msg : List UInt8) :
    SameView view (addMacToPacket pid msg) := by
  intro initial
  unfold addMacToPacket WG.andM
  material_lower
  repeat' first
    | material_known (fun t => t = initial)
    | material_basic (fun t => t = initial)

theorem sendBufferToPeer_material (pid : PeerId) (bytes : List UInt8) :
    SameView view (sendBufferToPeer pid bytes) := by
  intro initial
  unfold sendBufferToPeer
  material_lower
  repeat' first
    | (index_material_head send4; exact (send4_material _ _ _ _ _).wp (fun t => t = initial))
    | (index_material_head send6; exact (send6_material _ _ _ _ _).wp (fun t => t = initial))
    | material_known (fun t => t = initial)
    | material_basic (fun t => t = initial)

theorem sendHandshakeInitiation_material (pid : PeerId) : SameView view (sendHandshakeInitiation pid) := by
  intro initial
  unfold sendHandshakeInitiation
  material_lower
  repeat' first
    | (index_material_head createInitiation; exact (createInitiation_material _).wp (fun t => t = initial))
    | (index_material_head addMacToPacket; exact (addMacToPacket_material _ _).wp (fun t => t = initial))
    | (index_material_head timersTraversal; exact (timersTraversal_material _).wp (fun t => t = initial))
    | (index_material_head timersAnyAuthenticatedPacketSent; exact (timersAnyAuthenticatedPacketSent_material _).wp (fun t => t = initial))
    | (index_material_head sendBufferToPeer; exact (sendBufferToPeer_material _ _).wp (fun t => t = initial))
    | (index_material_head timersHandshakeInitiated; exact (timersHandshakeInitiated_material _).wp (fun t => t = initial))
    | material_known (fun t => t = initial)
    | material_basic (fun t => t = initial)

theorem createResponse_material (pid : PeerId) : SameView view (createResponse pid) := by
  intro initial
  unfold createResponse
  index_unfold _private.Leanux.WG.Handshake.«0».Leanux.WG.setChain
  material_lower
  repeat' first
    | material_known (fun t => t = initial)
    | material_basic (fun t => t = initial)

theorem timersSessionDerived_material (pid : PeerId) : SameView view (timersSessionDerived pid) := by
  intro initial
  unfold timersSessionDerived
  material_lower
  repeat' first
    | (index_material_head modPeerTimer; exact (modPeerTimer_material _ _ _ _).wp (fun t => t = initial))
    | material_known (fun t => t = initial)
    | material_basic (fun t => t = initial)

/-- The original arbitrary product modifier domain and 43-field cookie mask. -/
theorem cookie_material (a : Leanux.M α) (ha : SameView productCookieView a) :
    SameView (fun w : World => view w.wg) a := by
  apply ha.of_factor (fun k : ProductStore43 => k.2.2.2.dev.map materialState)
    (fun w : World => view w.wg)
  intro w
  simp only [productCookieView,cookieStoreView,cookieView,wgOwnedView,wgStoreView,
    cookieDevice,view,materialState,Option.map_map,Function.comp_def]

/-- Native callers use the same seven WG observations, without a stronger
routing/timer premise. -/
theorem cookie_material_native (a : WG.M α) (ha : SameView cookieStoreView a) :
    SameView view a := by
  apply ha.of_factor (fun k : WGStoreView => k.dev.map materialState) view
  intro w
  simp only [cookieStoreView,cookieView,wgOwnedView,wgStoreView,cookieDevice,
    view,materialState,Option.map_map,Function.comp_def]

theorem consumeInitiation_material (msg : List UInt8) : RetainsCall (consumeInitiation msg) := by
  apply ProjectedAction.of_wp
  intro initial
  let P := RetainsView initial
  apply hoare_consequence (P := fun w => P (view w)) (Q := fun _ w => P (view w))
    (a := consumeInitiation msg) ?_ (fun _ h => by
      dsimp only [id] at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold consumeInitiation WG.orM
  material_lower
  repeat' first
    | (index_material_head peerPut; exact (peerPut_material _).wp P)
    | (index_material_head pubkeyLookup; exact (pubkeyLookup_material _).wp P)
    | (index_material_head indexLookup; exact (indexLookup_retains _ _).wp P (fun _ _ hr hi => hi.trans hr))
    | material_known P
    | material_basic P

theorem consumeResponse_material (msg : List UInt8) : RetainsCall (consumeResponse msg) := by
  apply ProjectedAction.of_wp
  intro initial
  let P := RetainsView initial
  apply hoare_consequence (P := fun w => P (view w)) (Q := fun _ w => P (view w))
    (a := consumeResponse msg) ?_ (fun _ h => by
      dsimp only [id] at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold consumeResponse
  material_lower
  repeat' first
    | (index_material_head peerPut; exact (peerPut_material _).wp P)
    | (index_material_head pubkeyLookup; exact (pubkeyLookup_material _).wp P)
    | (index_material_head indexLookup; exact (indexLookup_retains _ _).wp P (fun _ _ hr hi => hi.trans hr))
    | material_known P
    | material_basic P

theorem cookieMessageConsume_material (msg : List UInt8) :
    RetainsCall (cookieMessageConsume msg) := by
  apply ProjectedAction.of_wp
  intro initial
  let P := RetainsView initial
  apply hoare_consequence (P := fun w => P (view w)) (Q := fun _ w => P (view w))
    (a := cookieMessageConsume msg) ?_ (fun _ h => by
      dsimp only [id] at h; rw [h]; exact RetainsView.refl _) (fun _ _ h => h)
  unfold cookieMessageConsume
  material_lower
  repeat' first
    | (index_material_head peerPut; exact (peerPut_material _).wp P)
    | (index_material_head pubkeyLookup; exact (pubkeyLookup_material _).wp P)
    | (index_material_head indexLookup; exact (indexLookup_retains _ _).wp P (fun _ _ hr hi => hi.trans hr))
    | material_known P
    | material_basic P

end Leanux.Proofs.WG.Origins.Retaining
