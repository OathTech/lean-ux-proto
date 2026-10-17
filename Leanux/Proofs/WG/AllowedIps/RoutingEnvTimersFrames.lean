import Leanux.Proofs.WG.AllowedIps.RoutingEnvWorkersFrames
import Leanux.Proofs.WG.Environment.TimerSource
import Leanux.Proofs.WG.AllowedIps.RoutingMaintenanceFrames

/-! The current timer-wheel loops and their idle/advance callers retain routing
on normal return. Native callbacks execute through the actual product adapter;
record order, wheel detachment and pass-step guards remain the source's.
The former raw-expiry selectors are no longer mirror operations. -/
namespace Leanux.Proofs.WG.AllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.WG.Lifetimes Std.Do
set_option maxHeartbeats 1000000
set_option pp.structureInstances false

open Lean Meta Elab Tactic

private def timerFrameAction (target : Expr) : MetaM Expr := do
  unless target.isAppOf ``Preserves && target.getAppArgs.size ≥ 2 do
    throwError "not a preservation contract"
  return target.getAppArgs.back!.consumeMData

elab "timer_frame_head " name:ident : tactic => withMainContext do
  let action ← timerFrameAction (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
  let rec head (fuel : Nat) (e : Expr) : Name :=
    match fuel with
    | 0 => .anonymous
    | n+1 =>
      let e := e.consumeMData
      if e.isAppOf ``MonadLift.monadLift || e.isAppOf ``MonadLiftT.monadLift || e.isAppOf ``liftM then
        if e.getAppArgs.isEmpty then .anonymous else head n e.getAppArgs.back!
      else
        match e.getAppFn with
        | .const name _ => name
        | _ => .anonymous
  let actual := head 4 action
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different preservation action"

elab "timer_frame_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let action ← timerFrameAction target
  let rec reduce : Nat → Expr → Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else reduce n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e
          else reduce n (mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Expr.equal e next then e else reduce n next
        | _ => e
  let next := reduce 64 action
  if Expr.equal action next then throwError "head unchanged"
  replaceMainGoal [← goal.replaceTargetDefEq (mkAppN target.getAppFn
    (target.getAppArgs.set! (target.getAppArgs.size - 1) next))]

elab "timer_frame_match" : tactic => withMainContext do
  let goal ← getMainGoal
  let action ← timerFrameAction (← instantiateMVars (← goal.getType)).consumeMData
  let some _ ← matchMatcherApp? action | throwError "not a head matcher"
  replaceMainGoal (← Split.splitMatch goal action)

elab "timer_frame_join" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let action ← timerFrameAction target
  let .letE name ty value body _ := action | throwError "not a shared continuation"
  unless name.toString.startsWith "__do_jp" do throwError "not a shared continuation"
  let pred := target.getAppArgs[target.getAppArgs.size - 2]!
  let property := fun a => mkAppM ``Preserves #[pred, a]
  let contract ← forallTelescope ty fun xs _ => do
    mkForallFVars xs (← property (mkAppN value xs))
  let valueProof ← mkFreshExprSyntheticOpaqueMVar contract
  let (proof, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun xs _ => do
      mkForallFVars xs (← property (mkAppN f xs))
    withLocalDeclD `timer_frame_continuation contract fun hf => do
      let next ← mkFreshExprSyntheticOpaqueMVar (← property (body.instantiate1 f))
      pure (← mkLambdaFVars #[f, hf] next, next.mvarId!)
  goal.assign (mkApp2 proof value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "timer_frame_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  let action ← timerFrameAction target
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `timer_frame_continuation then
      let proof := mkAppN decl.toExpr action.getAppArgs
      if ← withReducible (isDefEq (← inferType proof) target) then
        goal.assign proof
        replaceMainGoal []
        return
  throwError "no continuation contract"

theorem runTimerSection_routing (worker : Worker) (body : Leanux.M Unit)
    (hb : ProductRetainsRoutingCall body) :
    ProductRetainsRoutingCall (Env.runTimerSection worker body) := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Env.runTimerSection worker body) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w => P (routingView w.wg)) no) :
        Preserves (fun w => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w => P (routingView w.wg)) (body i b)) :
        Preserves (fun w => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have workerSpec := RetainsRoutingCall.wp (runWorker_routing worker body hb) s
    unfold Env.runTimerSection
    repeat' first
      | (timer_frame_head Env.runWorker; exact workerSpec)
      | timer_frame_join
      | timer_frame_join_use
      | (timer_frame_head getWG; exact readWG)
      | (timer_frame_head getDev; exact dev)
      | (timer_frame_head getEnv; exact readEnv)
      | (timer_frame_head modifyWG; exact edit _ (fun _ => rfl))
      | (timer_frame_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (timer_frame_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (timer_frame_head invariant; exact ambient (AmbientM.invariant _))
      | (timer_frame_head unsupported; exact ambient (AmbientM.unsupported _))
      | (timer_frame_head recordBudget; exact ambient AmbientM.recordBudget)
      | (timer_frame_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (timer_frame_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (timer_frame_head hiddenJiffies; exact ambient (AmbientM.hiddenJiffies _))
      | (timer_frame_head Env.peekNextSite; exact peek)
      | (timer_frame_head Functor.discard; apply discardSpec)
      | (timer_frame_head throw; exact hoare_throw _)
      | (timer_frame_head MonadExceptOf.throw; exact hoare_throw _)
      | (timer_frame_head Pure.pure; exact preserves_pure _)
      | (timer_frame_head Bind.bind; apply preserves_bind)
      | (timer_frame_head ForIn.forIn; apply loop)
      | (timer_frame_head ite; apply choose)
      | maintenance_intro
      | timer_frame_reduce
      | timer_frame_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

private theorem requireStepComplete_routing (b : UInt64) :
    SameView (fun w : World => routingView w.wg) (Env.requireStepComplete b) := by
  intro s
  change Preserves (fun w : World => routingView w.wg = s) (Env.requireStepComplete b)
  have dev := productGetDev_spec (fun store => store.2.2.2.dev.map routingState = s)
  unfold Env.requireStepComplete
  apply preserves_bind dev
  intro d
  cases TimerWheel.anotherAtStep d b with
  | none => exact preserves_pure _
  | some due =>
    rcases due with ⟨pid, t⟩
    exact hoare_throw _

private theorem requireNothingDue_routing (jPass : UInt64) :
    SameView (fun w : World => routingView w.wg) (Env.requireNothingDue jPass) := by
  apply (Leanux.Proofs.WG.Lifetimes.ProjectedAction.iff_run _ _ _).mpr
  intro w x w' hr
  have read (s : World) : (getWG : Leanux.M WGWorld).run s = .ok (s.wg, s) := rfl
  unfold Env.requireNothingDue at hr
  simp only [StateT.run_bind, read, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
  cases hd : w.wg.dev with
  | none =>
    simp only [hd, StateT.run_pure] at hr
    cases hr
    rfl
  | some d =>
    simp only [hd] at hr
    cases hn : TimerWheel.nextDue d jPass with
    | none =>
      simp only [hn, StateT.run_pure] at hr
      cases hr
      rfl
    | some due =>
      rcases due with ⟨pid, t, we⟩
      simp only [hn, StateT.run_bind] at hr
      cases hw : (Env.timerWorker t).run w with
      | error e =>
        rw [hw] at hr
        cases hr
      | ok out =>
        rcases out with ⟨worker, w1⟩
        simp only [hw, Leanux.Proofs.WG.CounterWindow.except_ok_bind, read] at hr
        cases hs : (Env.sectionAppearsLater worker
          (((w1.wg.timerUnits.find? fun e => e.2.1 == pid && e.2.2 == t).map (·.1)).getD 0)).run w1 with
        | error e =>
          rw [hs] at hr
          cases hr
        | ok out =>
          rcases out with ⟨later, w2⟩
          simp only [hs, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
          cases later <;> cases hr

theorem runTimers_routing (jHi : UInt64) :
    ProductRetainsRoutingCall (Env.runTimers jHi) := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Env.runTimers jHi) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w => P (routingView w.wg)) no) :
        Preserves (fun w => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w => P (routingView w.wg)) (body i b)) :
        Preserves (fun w => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have detach (pid : PeerId) (t : PeerTimer) :=
      (sameView_liftWG (fun w : World => routingView w.wg) routingView (delTimer pid t)
        (delTimer_routing pid t) (fun _ _ _ h => h)).wp P
    have callback (worker : Worker) (pid : PeerId) (t : PeerTimer) :=
      RetainsRoutingCall.wp
        (runTimerSection_routing worker _ (timerCallback_routing pid t).liftWG) s
    have step (b : UInt64) := (requireStepComplete_routing b).wp P
    have timer (t : PeerTimer) := ((timerWorker_sameKernel t).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl)).wp P
    have clear := RetainsRoutingCall.wp runOneClearWorker_routing s
    have send := RetainsRoutingCall.wp runOneSendWorker_routing s
    have crypt := RetainsRoutingCall.wp runCryptWorkers_routing s
    have deliver := deliverSent_routing.wp P
    unfold Env.runTimers
    repeat' first
      | (timer_frame_head delTimer; exact detach _ _)
      | (timer_frame_head Env.runTimerSection; exact callback _ _ _)
      | (timer_frame_head Env.requireStepComplete; exact step _)
      | (timer_frame_head Env.timerWorker; exact timer _)
      | (timer_frame_head Env.runOneClearWorker; exact clear)
      | (timer_frame_head Env.runOneSendWorker; exact send)
      | (timer_frame_head Env.runCryptWorkers; exact crypt)
      | (timer_frame_head Env.deliverSent; exact deliver)
      | timer_frame_join
      | timer_frame_join_use
      | (timer_frame_head getWG; exact readWG)
      | (timer_frame_head getDev; exact dev)
      | (timer_frame_head getEnv; exact readEnv)
      | (timer_frame_head modifyWG; exact edit _ (fun _ => rfl))
      | (timer_frame_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (timer_frame_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (timer_frame_head invariant; exact ambient (AmbientM.invariant _))
      | (timer_frame_head unsupported; exact ambient (AmbientM.unsupported _))
      | (timer_frame_head recordBudget; exact ambient AmbientM.recordBudget)
      | (timer_frame_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (timer_frame_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (timer_frame_head hiddenJiffies; exact ambient (AmbientM.hiddenJiffies _))
      | (timer_frame_head Env.peekNextSite; exact peek)
      | (timer_frame_head Functor.discard; apply discardSpec)
      | (timer_frame_head throw; exact hoare_throw _)
      | (timer_frame_head MonadExceptOf.throw; exact hoare_throw _)
      | (timer_frame_head Pure.pure; exact preserves_pure _)
      | (timer_frame_head Bind.bind; apply preserves_bind)
      | (timer_frame_head ForIn.forIn; apply loop)
      | (timer_frame_head ite; apply choose)
      | maintenance_intro
      | timer_frame_reduce
      | timer_frame_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem runTimersPlaceholder_routing (jHi : UInt64) :
    ProductRetainsRoutingCall (Env.runTimersPlaceholder jHi) := by
  rw [← Environment.runTimersPlaceholderSource_eq]
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Environment.runTimersPlaceholderSource jHi) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w => P (routingView w.wg)) no) :
        Preserves (fun w => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w => P (routingView w.wg)) (body i b)) :
        Preserves (fun w => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have detach (pid : PeerId) (t : PeerTimer) :=
      (sameView_liftWG (fun w : World => routingView w.wg) routingView (delTimer pid t)
        (delTimer_routing pid t) (fun _ _ _ h => h)).wp P
    have callback (worker : Worker) (pid : PeerId) (t : PeerTimer) :=
      RetainsRoutingCall.wp
        (runTimerSection_routing worker _ (timerCallback_routing pid t).liftWG) s
    have timer (t : PeerTimer) := ((timerWorker_sameKernel t).of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl)).wp P
    have clear := RetainsRoutingCall.wp runOneClearWorker_routing s
    have send := RetainsRoutingCall.wp runSendWorkers_routing s
    have crypt := RetainsRoutingCall.wp runCryptWorkers_routing s
    unfold Environment.runTimersPlaceholderSource
    repeat' first
      | (timer_frame_head delTimer; exact detach _ _)
      | (timer_frame_head Env.runTimerSection; exact callback _ _ _)
      | (timer_frame_head Env.timerWorker; exact timer _)
      | (timer_frame_head Env.runOneClearWorker; exact clear)
      | (timer_frame_head Env.runSendWorkers; exact send)
      | (timer_frame_head Env.runCryptWorkers; exact crypt)
      | timer_frame_join
      | timer_frame_join_use
      | (timer_frame_head getWG; exact readWG)
      | (timer_frame_head getDev; exact dev)
      | (timer_frame_head getEnv; exact readEnv)
      | (timer_frame_head modifyWG; exact edit _ (fun _ => rfl))
      | (timer_frame_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (timer_frame_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (timer_frame_head invariant; exact ambient (AmbientM.invariant _))
      | (timer_frame_head unsupported; exact ambient (AmbientM.unsupported _))
      | (timer_frame_head recordBudget; exact ambient AmbientM.recordBudget)
      | (timer_frame_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (timer_frame_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (timer_frame_head hiddenJiffies; exact ambient (AmbientM.hiddenJiffies _))
      | (timer_frame_head Env.peekNextSite; exact peek)
      | (timer_frame_head Functor.discard; apply discardSpec)
      | (timer_frame_head throw; exact hoare_throw _)
      | (timer_frame_head MonadExceptOf.throw; exact hoare_throw _)
      | (timer_frame_head Pure.pure; exact preserves_pure _)
      | (timer_frame_head Bind.bind; apply preserves_bind)
      | (timer_frame_head ForIn.forIn; apply loop)
      | (timer_frame_head ite; apply choose)
      | maintenance_intro
      | timer_frame_reduce
      | timer_frame_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem idleTimers_routing : ProductRetainsRoutingCall Env.idleTimers := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Env.idleTimers) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w => P (routingView w.wg)) no) :
        Preserves (fun w => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w => P (routingView w.wg)) (body i b)) :
        Preserves (fun w => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have timers (j : UInt64) := RetainsRoutingCall.wp (runTimers_routing j) s
    have placeholder (j : UInt64) := RetainsRoutingCall.wp (runTimersPlaceholder_routing j) s
    have noneDue (j : UInt64) := (requireNothingDue_routing j).wp P
    unfold Env.idleTimers
    repeat' first
      | (timer_frame_head Env.runTimers; exact timers _)
      | (timer_frame_head Env.runTimersPlaceholder; exact placeholder _)
      | (timer_frame_head Env.requireNothingDue; exact noneDue _)
      | timer_frame_join
      | timer_frame_join_use
      | (timer_frame_head getWG; exact readWG)
      | (timer_frame_head getDev; exact dev)
      | (timer_frame_head getEnv; exact readEnv)
      | (timer_frame_head modifyWG; exact edit _ (fun _ => rfl))
      | (timer_frame_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (timer_frame_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (timer_frame_head invariant; exact ambient (AmbientM.invariant _))
      | (timer_frame_head unsupported; exact ambient (AmbientM.unsupported _))
      | (timer_frame_head recordBudget; exact ambient AmbientM.recordBudget)
      | (timer_frame_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (timer_frame_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (timer_frame_head hiddenJiffies; exact ambient (AmbientM.hiddenJiffies _))
      | (timer_frame_head Env.peekNextSite; exact peek)
      | (timer_frame_head Functor.discard; apply discardSpec)
      | (timer_frame_head throw; exact hoare_throw _)
      | (timer_frame_head MonadExceptOf.throw; exact hoare_throw _)
      | (timer_frame_head Pure.pure; exact preserves_pure _)
      | (timer_frame_head Bind.bind; apply preserves_bind)
      | (timer_frame_head ForIn.forIn; apply loop)
      | (timer_frame_head ite; apply choose)
      | maintenance_intro
      | timer_frame_reduce
      | timer_frame_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

theorem advance_routing (ticks : Nat) :
    SameView (fun w : World => routingView w.wg) (Env.advance ticks) :=
  (advance_sameKernel ticks).of_factor
    (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
    (fun w : World => routingView w.wg) (fun _ => rfl)

theorem afterAdvance_routing : ProductRetainsRoutingCall Env.afterAdvance := by
  intro s
  let P := RetainsRouting s
  have main : Preserves (fun w : World => P (routingView w.wg)) (Env.afterAdvance) := by
    have ambient {α : Type} (a : AmbientM α) :
        Preserves (fun w : World => P (routingView w.wg)) (monadLift a : Leanux.M α) :=
      productAmbient_spec a _ (fun _ _ h => h)
    have dev := productGetDev_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readWG := productGetWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have edit := productModifyWG_spec (fun store => P (store.2.2.2.dev.map routingState))
    have readEnv : Preserves (fun w : World => P (routingView w.wg)) getEnv := by
      apply (hoare_iff_run _ _ _).mpr
      intro w x v hi hr
      cases hr
      exact hi
    have choose {α : Type} (condition : Prop) [Decidable condition] (yes no : Leanux.M α)
        (hy : condition → Preserves (fun w => P (routingView w.wg)) yes)
        (hn : ¬condition → Preserves (fun w => P (routingView w.wg)) no) :
        Preserves (fun w => P (routingView w.wg)) (if condition then yes else no) := by
      split
      · apply hy; assumption
      · apply hn; assumption
    have loop {β : Type} (range : Std.Legacy.Range) (initial : β)
        (body : Nat → β → Leanux.M (ForInStep β))
        (hb : ∀ i b, Preserves (fun w => P (routingView w.wg)) (body i b)) :
        Preserves (fun w => P (routingView w.wg)) (forIn range initial body) := by
      rw [Std.Legacy.Range.forIn_eq_forIn_range']
      exact list_view_spec (fun w : World => routingView w.wg) P _ _ _ hb
    have discardSpec {α : Type} (a : Leanux.M α)
        (ha : Preserves (fun w : World => P (routingView w.wg)) a) :
        Preserves (fun w : World => P (routingView w.wg)) (discard a) :=
      discard_view_spec (fun w : World => routingView w.wg) P a ha
    have peek := peekNextSite_sameKernel.of_factor
      (fun store : ProductStore43 => store.2.2.2.dev.map routingState)
      (fun w : World => routingView w.wg) (fun _ => rfl) |>.wp P
    have timers (j : UInt64) := RetainsRoutingCall.wp (runTimers_routing j) s
    have placeholder (j : UInt64) := RetainsRoutingCall.wp (runTimersPlaceholder_routing j) s
    have noneDue (j : UInt64) := (requireNothingDue_routing j).wp P
    unfold Env.afterAdvance
    repeat' first
      | (timer_frame_head Env.runTimers; exact timers _)
      | (timer_frame_head Env.runTimersPlaceholder; exact placeholder _)
      | (timer_frame_head Env.requireNothingDue; exact noneDue _)
      | timer_frame_join
      | timer_frame_join_use
      | (timer_frame_head getWG; exact readWG)
      | (timer_frame_head getDev; exact dev)
      | (timer_frame_head getEnv; exact readEnv)
      | (timer_frame_head modifyWG; exact edit _ (fun _ => rfl))
      | (timer_frame_head getAmbient; exact ambient (get : AmbientM Ambient))
      | (timer_frame_head modifyAmbient; exact ambient (modify _ : AmbientM Unit))
      | (timer_frame_head invariant; exact ambient (AmbientM.invariant _))
      | (timer_frame_head unsupported; exact ambient (AmbientM.unsupported _))
      | (timer_frame_head recordBudget; exact ambient AmbientM.recordBudget)
      | (timer_frame_head peekUnit; exact ambient (AmbientM.peekUnit _))
      | (timer_frame_head peekSiteU64; exact ambient (AmbientM.peekSiteU64 _))
      | (timer_frame_head hiddenJiffies; exact ambient (AmbientM.hiddenJiffies _))
      | (timer_frame_head Env.peekNextSite; exact peek)
      | (timer_frame_head Functor.discard; apply discardSpec)
      | (timer_frame_head throw; exact hoare_throw _)
      | (timer_frame_head MonadExceptOf.throw; exact hoare_throw _)
      | (timer_frame_head Pure.pure; exact preserves_pure _)
      | (timer_frame_head Bind.bind; apply preserves_bind)
      | (timer_frame_head ForIn.forIn; apply loop)
      | (timer_frame_head ite; apply choose)
      | maintenance_intro
      | timer_frame_reduce
      | timer_frame_match
  apply hoare_consequence main
  · intro w he
    change RetainsRouting s (routingView w.wg)
    change routingView w.wg = s at he
    rw [he]
    exact RetainsRouting.refl _
  · exact fun _ _ h => h

end Leanux.Proofs.WG.AllowedIps
