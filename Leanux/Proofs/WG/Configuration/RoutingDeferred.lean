import Leanux.Proofs.WG.Configuration.RoutingEnvironment
import Leanux.Proofs.WG.AllowedIps.RoutingEnvControlsCompletion
import Leanux.Proofs.WG.Queues.RxEnvTimersHistory

/-! Positional routing through the original deferred observers. Audit leaves
are quiet for consume entries; actual polls retain their exact capture prefixes. -/
namespace Leanux.Proofs.WG.RoutingPosition.Deferred
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues AllowedIps Origins RoutingPosition.Callers

private theorem audit_store (initial : FlatTable × FlatTable) (g : AuditM α)
    (a : Leanux.M α) (erases : ErasesPrefix g a) (frame : SameProductStore a) :
    Focused initial (RxHistory.audit g) :=
  audit initial g a erases
    ((pinned_const _private.Leanux.Proofs.WG.Configuration.RoutingEnvironment.«0».Leanux.Proofs.WG.RoutingPosition.Environment.store_frame) a frame)

private theorem sendOne (initial : FlatTable × FlatTable) :
    Focused initial (RxHistory.audit runOneSendWorkerAudit) :=
  audit initial _ _ runOneSendWorkerAudit_erases runOneSendWorker_routing

private theorem clearOne (initial : FlatTable × FlatTable) :
    Focused initial (RxHistory.audit runOneClearWorkerAudit) :=
  audit initial _ _ runOneClearWorkerAudit_erases runOneClearWorker_routing

private theorem drained (initial : FlatTable × FlatTable) (what : String) (queues : List Bool) :
    Focused initial (RxHistory.mixed (requireDrainedPrefix what queues)) :=
  mixed initial _ _ (requireDrainedPrefix_erases _ _)
    (ProjectedRetainsRoutingCall.of_same (requireDrained_routing _ _))

open Lean Meta Elab Tactic in
elab "routing_deferred_audit_at " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``Focused || target.isAppOf ``FocusedInvariant do throwError "not routing focus"
  let fields := target.getAppArgs
  unless fields.size > 0 do throwError "missing observer"
  let action := fields.back!.consumeMData
  unless action.isAppOf ``RxHistory.audit do throwError "not audit focus"
  let parts := action.getAppArgs
  unless parts.size > 0 do throwError "missing audit observer"
  let expected ← realizeGlobalConstNoOverloadWithInfo wanted
  unless parts.back!.consumeMData.getAppFn.constName? == some expected do throwError "different audit observer"

macro "routing_deferred_steps " initial:term : tactic => `(tactic| first
  | (routing_env_at Env.deliverSent; exact store $initial _ deliverSent_sameKernel)
  | (routing_env_at Env.requireNoCryptWork; exact store $initial _ requireNoCryptWork_sameKernel)
  | (routing_env_at getWG
     exact store $initial _ (fun state => productGetWG_spec (fun s => s = state)))
  | (routing_env_at modifyWG
     exact store $initial _ (fun state => productModifyWG_spec (fun s => s = state) _ (fun _ => rfl)))
  | (routing_deferred_audit_at runOneSendWorkerAudit; exact sendOne $initial)
  | (routing_deferred_audit_at runOneClearWorkerAudit; exact clearOne $initial)
  | (routing_env_at requireDrainedPrefix; exact drained $initial _ _)
  | routing_env_steps $initial)

theorem runCryptWorkers (initial : FlatTable × FlatTable) :
    Focused initial RxHistory.runCryptWorkers :=
  bind initial _ _ (Environment.schedule initial none)
    (fun _ => store initial _ deliverSent_sameKernel)

theorem runSendWorkers (initial : FlatTable × FlatTable) :
    Focused initial RxHistory.runSendWorkers := by
  unfold RxHistory.runSendWorkers
  repeat' first
    | (routing_env_at RxHistory.schedule; exact Environment.schedule initial _)
    | routing_deferred_steps initial

theorem afterXmit (initial : FlatTable × FlatTable) :
    Focused initial RxHistory.afterXmit := by
  unfold RxHistory.afterXmit
  repeat' first
    | (routing_env_at RxHistory.runCryptWorkers; exact runCryptWorkers initial)
    | (routing_env_at RxHistory.runSendWorkers; exact runSendWorkers initial)
    | routing_deferred_steps initial

private theorem retained (a : Leanux.M α)
    (ha : ∀ s, Preserves (fun w : World => RetainsRouting s (routingView w.wg)) a) :
    ProductRetainsRoutingCall a := by
  intro s
  apply hoare_consequence (ha s)
  · intro w he
    change routingView w.wg = s at he
    change RetainsRouting s (routingView w.wg)
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ hi => hi

private theorem timerDispatch_frame (worker : Worker) (pid : PeerId) (timer : PeerTimer)
    (we : WheelEntry) (prior : Option UInt64) :
    ProductRetainsRoutingCall (timerDispatchUnit worker pid timer we prior) := by
  apply retained
  intro s
  let P := RetainsRouting s
  have ambient {α : Type} (a : AmbientM α) : Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
  have timer (t : PeerTimer) := ((timerWorker_sameKernel t).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)).wp P
  have detach (p : PeerId) (t : PeerTimer) :=
    (sameView_liftWG (fun w : World => routingView w.wg) routingView (delTimer p t)
      (delTimer_routing p t) (fun _ _ _ hi => hi)).wp P
  have sectionSpec (worker : Worker) (p : PeerId) (t : PeerTimer) :=
    RetainsRoutingCall.wp (runTimerSection_routing worker _ (timerCallback_routing p t).liftWG) s
  have step (b : UInt64) :=
    ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames.«0».Leanux.Proofs.WG.AllowedIps.requireStepComplete_routing) b).wp P
  unfold timerDispatchUnit
  repeat' first
    | (timer_frame_head Env.runTimerSection; exact sectionSpec _ _ _)
    | (timer_frame_head Env.requireStepComplete; exact step _)
    | (timer_frame_head Env.timerWorker; exact timer _)
    | (timer_frame_head delTimer; exact detach _ _)
    | (timer_frame_head getWG; exact readWG)
    | (timer_frame_head modifyWG; exact edit _ (fun _ => rfl))
    | (timer_frame_head peekUnit; exact ambient (AmbientM.peekUnit _))
    | (timer_frame_head throw; exact hoare_throw _)
    | (timer_frame_head MonadExceptOf.throw; exact hoare_throw _)
    | (timer_frame_head Pure.pure; exact preserves_pure _)
    | (timer_frame_head Bind.bind; apply preserves_bind)
    | (timer_frame_head ite; split)
    | timer_frame_join
    | timer_frame_join_use
    | timer_frame_reduce
    | timer_frame_match
    | support_intro

private theorem placeholder_frame (j : UInt64) :
    ProductRetainsRoutingCall (RxHistory.placeholderTimerPassSource j) := by
  apply retained
  intro s
  let P := RetainsRouting s
  have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
  have timer (t : PeerTimer) := ((timerWorker_sameKernel t).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)).wp P
  have detach (p : PeerId) (t : PeerTimer) :=
    (sameView_liftWG (fun w : World => routingView w.wg) routingView (delTimer p t)
      (delTimer_routing p t) (fun _ _ _ hi => hi)).wp P
  have sectionSpec (worker : Worker) (p : PeerId) (t : PeerTimer) :=
    RetainsRoutingCall.wp (runTimerSection_routing worker _ (timerCallback_routing p t).liftWG) s
  have loop {β : Type} (r : Std.Legacy.Range) (first : β)
      (f : Nat → β → Leanux.M (ForInStep β))
      (hf : ∀ i b, Preserves (fun w : World => P (routingView w.wg)) (f i b)) :
      Preserves (fun w : World => P (routingView w.wg)) (forIn r first f) := by
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hf
  unfold RxHistory.placeholderTimerPassSource
  repeat' first
    | (timer_frame_head Env.runTimerSection; exact sectionSpec _ _ _)
    | (timer_frame_head Env.timerWorker; exact timer _)
    | (timer_frame_head delTimer; exact detach _ _)
    | (timer_frame_head getDev; exact dev)
    | (timer_frame_head Pure.pure; exact preserves_pure _)
    | (timer_frame_head Bind.bind; apply preserves_bind)
    | (timer_frame_head ForIn.forIn; apply loop)
    | (timer_frame_head ite; split)
    | timer_frame_join
    | timer_frame_join_use
    | timer_frame_reduce
    | timer_frame_match
    | support_intro

private theorem saved (initial : FlatTable × FlatTable) :
    Focused initial (RxHistory.audit getDevSavedAudit) :=
  audit_store initial _ _ getDevSavedAudit_erases (liftWG_sameProductStore getDev getDev_sameWGStore)

private theorem wheel (initial : FlatTable × FlatTable) (d : Device) (j : UInt64) :
    Focused initial (RxHistory.audit (wheelNextDueAudit d j)) :=
  audit_store initial _ _ (wheelNextDueAudit_erases d j) (SameView.pure _ _)

private theorem stepComplete (initial : FlatTable × FlatTable) (b : UInt64) :
    Focused initial (RxHistory.audit (requireStepCompleteAudit b)) :=
  audit initial _ _ (requireStepCompleteAudit_erases b) (ProjectedRetainsRoutingCall.of_same
    ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames.«0».Leanux.Proofs.WG.AllowedIps.requireStepComplete_routing) b))

private theorem nothingDue (initial : FlatTable × FlatTable) (j : UInt64) :
    Focused initial (RxHistory.audit (requireNothingDueAudit j)) :=
  audit initial _ _ (requireNothingDueAudit_erases j) (ProjectedRetainsRoutingCall.of_same
    ((pinned_const _private.Leanux.Proofs.WG.AllowedIps.RoutingEnvTimersFrames.«0».Leanux.Proofs.WG.AllowedIps.requireNothingDue_routing) j))

private theorem timerDispatch (initial : FlatTable × FlatTable) (worker : Worker) (pid : PeerId)
    (timer : PeerTimer) (we : WheelEntry) (prior : Option UInt64) :
    Focused initial (RxHistory.audit (timerDispatchAudit worker pid timer we prior)) :=
  audit initial _ _ (timerDispatchAudit_erases worker pid timer we prior)
    (timerDispatch_frame worker pid timer we prior)

private theorem placeholderPass (initial : FlatTable × FlatTable) (j : UInt64) :
    Focused initial (RxHistory.audit (RxHistory.placeholderTimerPassAudit j)) :=
  audit initial _ _ (RxHistory.placeholderTimerPass_erases j) (placeholder_frame j)

open Lean Meta Elab Tactic in
elab "routing_focus_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Focused || target.isAppOf ``FocusedInvariant do
    throwError "not an environment support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let rec head : Nat → Expr → Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else head n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e
          else head n (mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Expr.equal e next then e else head n next
        | _ => e
  let i := args.size - 1
  let action := args[i]!
  let reduced := head 64 action
  if Expr.equal action reduced then throwError "unchanged observer head"
  replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn (args.set! i reduced))]

open Lean Meta Elab Tactic in
elab "routing_focus_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Focused || target.isAppOf ``FocusedInvariant do
    throwError "not an environment support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let i := args.size - 1
  let action := args[i]!.consumeMData
  let .letE name ty value body _ := action | throwError "not a shared continuation"
  unless name.toString.startsWith "__do_jp" do throwError "not a shared continuation"
  let property := fun a => mkAppN target.getAppFn (args.set! i a)
  let contract ← forallTelescope ty fun xs _ => mkForallFVars xs (property (mkAppN value xs))
  let valueProof ← mkFreshExprSyntheticOpaqueMVar contract
  let (proof, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun xs _ => mkForallFVars xs (property (mkAppN f xs))
    withLocalDeclD `routing_focus_continuation contract fun hf => do
      let next ← mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 f))
      pure (← mkLambdaFVars #[f,hf] next, next.mvarId!)
  goal.assign (mkApp2 proof value valueProof)
  replaceMainGoal [valueProof.mvarId!,next]

open Lean Meta Elab Tactic in
elab "routing_focus_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Focused || target.isAppOf ``FocusedInvariant do
    throwError "not an environment support contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing observer"
  let action := args.back!.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `routing_focus_continuation then
      let proof := mkAppN decl.toExpr action.getAppArgs
      if ← withReducible (isDefEq (← inferType proof) target) then
        goal.assign proof
        replaceMainGoal []
        return
  throwError "no continuation contract"

macro "routing_timer_steps " initial:term : tactic => `(tactic| first
  | (routing_deferred_audit_at RxHistory.placeholderTimerPassAudit; exact placeholderPass $initial _)
  | (routing_deferred_audit_at wheelNextDueAudit; exact wheel $initial _ _)
  | (routing_deferred_audit_at timerDispatchAudit; exact timerDispatch $initial _ _ _ _ _)
  | (routing_deferred_audit_at requireStepCompleteAudit; exact stepComplete $initial _)
  | (routing_deferred_audit_at requireNothingDueAudit; exact nothingDue $initial _)
  | (routing_deferred_audit_at getDevSavedAudit; exact saved $initial)
  | (routing_env_at peekSiteU64; exact store $initial _ (fun state => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (routing_env_at hiddenJiffies; exact store $initial _ (fun state => productAmbient_spec _ _ (fun _ _ hi => hi)))
  | (routing_env_at getEnv
     exact store $initial _ (by
       apply (ProjectedAction.iff_run _ _ _).mpr
       intro w x v hr
       cases hr
       rfl))
  | (routing_env_at throw; exact store $initial _ (fun _ => hoare_throw _))
  | (routing_env_at Env.peekNextSite; exact store $initial _ peekNextSite_sameKernel)
  | (routing_env_at Env.timerWorker; exact store $initial _ (timerWorker_sameKernel _))
  | routing_focus_reduce
  | routing_focus_join
  | routing_focus_join_use
  | routing_deferred_steps $initial)

theorem runTimers (initial : FlatTable × FlatTable) (j : UInt64) :
    Focused initial (RxHistory.runTimers j) := by
  unfold RxHistory.runTimers
  repeat' first
    | (routing_env_at RxHistory.runCryptWorkers; exact runCryptWorkers initial)
    | routing_timer_steps initial

theorem runTimersPlaceholder (initial : FlatTable × FlatTable) (j : UInt64) :
    Focused initial (RxHistory.runTimersPlaceholder j) := by
  unfold RxHistory.runTimersPlaceholder
  repeat' first
    | (routing_env_at RxHistory.runCryptWorkers; exact runCryptWorkers initial)
    | (routing_env_at RxHistory.runSendWorkers; exact runSendWorkers initial)
    | routing_timer_steps initial

theorem idleTimers (initial : FlatTable × FlatTable) : Focused initial RxHistory.idleTimers := by
  unfold RxHistory.idleTimers
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (routing_env_at RxHistory.runTimers; exact runTimers initial _)
    | (routing_env_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder initial _)
    | routing_timer_steps initial

theorem afterAdvance (initial : FlatTable × FlatTable) : Focused initial RxHistory.afterAdvance := by
  unfold RxHistory.afterAdvance
  simp only [discard,map_const,Function.comp_def,map_eq_pure_bind,bind_assoc]
  repeat' first
    | (routing_env_at RxHistory.runTimers; exact runTimers initial _)
    | (routing_env_at RxHistory.runTimersPlaceholder; exact runTimersPlaceholder initial _)
    | routing_timer_steps initial

/-- Every original deferred call preserves the routing state and the routing
fact captured at each consumed receipt, including all stopped prefixes. -/
theorem deferred (initial : FlatTable × FlatTable) (call : EnvDeferredCall) :
    Focused initial (RxHistory.deferred call) := by
  cases call with
  | drained what queues => exact drained initial what queues
  | idleDevice =>
    exact mixed initial _ _ requireIdleDevicePrefix_erases
      (ProjectedRetainsRoutingCall.of_same requireIdleDevice_routing)
  | noCrypt => exact audit_store initial _ _ (erasesPrefix_lift _) requireNoCryptWork_sameKernel
  | crypt => exact runCryptWorkers initial
  | sendOne => exact sendOne initial
  | clearOne => exact clearOne initial
  | sendAll => exact runSendWorkers initial
  | afterXmit => exact afterXmit initial
  | timerWorker timer => exact audit_store initial _ _ (erasesPrefix_lift _) (timerWorker_sameKernel timer)
  | timers j => exact runTimers initial j
  | placeholder j => exact runTimersPlaceholder initial j
  | idle => exact idleTimers initial
  | advance ticks => exact audit_store initial _ _ (erasesPrefix_lift _) (advance_sameKernel ticks)
  | afterAdvance => exact afterAdvance initial

end Leanux.Proofs.WG.RoutingPosition.Deferred
