import Leanux.Proofs.WG.AuthenticatedEffects.CausalCoverageFlow

/-! A concrete lexical entry establishes the nonempty context required by its
own effectful body. Normal completion pops that exact token; no arbitrary caller
is granted a context by this contract. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
open Leanux Leanux.WG Leanux.Proofs.Logged

theorem state_scope (cause : Cause) (other : Other cause) (body : WGPrefix Event α) (covered : StateGuarded body) :
    StateClosed (CausalScope.scope Event.scope cause body) := by
  intro frames w a h ready
  let token : CausalScope.Token Cause := ⟨h.length,cause⟩
  let entered := h ++ [.scope (.entered token)]
  have entry : Inv (token :: frames) entered := ready.enter token other
  obtain ⟨suffix,grown,safe,normal⟩ := covered (token :: frames) (by simp) w a entered entry
  change (runWGPrefix body w a entered).2 = entered ++ suffix at grown
  change Safe (runWGPrefix body w a entered).2 at safe
  have equation := CausalScope.withToken_run Event.scope cause (fun _ => body) w a h
  change runPrefix (StateT.run (CausalScope.scope Event.scope cause body) w) a h = _ at equation
  cases run : runWGPrefix body w a entered with
  | mk result history =>
    rw [run] at grown safe
    change history = entered ++ suffix at grown
    have normalRun := run
    change runPrefix (body.run w) a entered = (result,history) at normalRun
    rw [normalRun] at normal
    dsimp only [token,entered] at run
    rw [run] at equation
    rw [equation]
    cases result with
    | error stop =>
      exact ⟨.scope (.entered token) :: suffix,
        by simpa only [entered,List.append_assoc,List.singleton_append] using grown,safe,True.intro⟩
    | ok result =>
      rcases result with ⟨⟨value,v⟩,b⟩
      have exited := Inv.leave normal
      exact ⟨.scope (.entered token) :: (suffix ++ [.scope (.exited h.length)]),
        by simp only [grown,entered,List.append_assoc,List.cons_append,List.nil_append],exited.1,exited⟩

theorem product_scope (cause : Cause) (other : Other cause) (body : CausalScope.Token Cause → PrefixM Event α)
    (covered : ∀ token, ProductGuarded (body token)) :
    ProductClosed (CausalScope.prefixScope Event.scope cause body) := by
  intro frames w h ready
  let token : CausalScope.Token Cause := ⟨h.length,cause⟩
  let entered := h ++ [.scope (.entered token)]
  have entry : Inv (token :: frames) entered := ready.enter token other
  obtain ⟨suffix,grown,safe,normal⟩ := covered token (token :: frames) (by simp) w entered entry
  have equation := CausalScope.prefix_run Event.scope cause body w h
  cases run : runPrefix (body token) w entered with
  | mk result history =>
    rw [run] at grown safe normal
    change history = entered ++ suffix at grown
    change Safe history at safe
    dsimp only [token,entered] at run
    rw [run] at equation
    rw [equation]
    cases result with
    | error stop =>
      exact ⟨.scope (.entered token) :: suffix,
        by simpa only [entered,List.append_assoc,List.singleton_append] using grown,safe,True.intro⟩
    | ok result =>
      rcases result with ⟨value,v⟩
      have exited := Inv.leave normal
      exact ⟨.scope (.entered token) :: (suffix ++ [.scope (.exited h.length)]),
        by simp only [grown,entered,List.append_assoc,List.cons_append,List.nil_append],exited.1,exited⟩

open Lean Meta Elab Tactic in
elab "coverage_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateAt || target.isAppOf ``ProductAt do throwError "not a coverage contract"
  let args := target.getAppArgs
  unless args.size > 0 do throwError "missing action"
  let action := args.back!.consumeMData.headBeta
  let action ← if action.isAppOf ``liftWGObserver then do
    let inner := action.getAppArgs
    unless inner.size > 0 do throwError "missing lifted action"
    pure inner.back!.consumeMData
    else pure action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

open Lean Meta Elab Tactic in
elab "coverage_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateAt || target.isAppOf ``ProductAt do throwError "not a coverage contract"
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
          if name.toString.startsWith "__do_jp" then e else head n (mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Expr.equal e next then e else head n next
        | _ => e
  let .app f action := target | throwError "missing action"
  let next := if action.isAppOf ``liftWGObserver then
      match action with
      | .app outer inner => mkApp outer (head 64 inner)
      | _ => action
    else head 64 action
  if Expr.equal action next then throwError "head unchanged"
  replaceMainGoal [← goal.replaceTargetDefEq (mkApp f next)]

macro "coverage_state_step" : tactic => `(tactic| first
  | (coverage_head liftWGPrefix; exact state_lift _)
  | (coverage_head Pure.pure; exact state_pure _)
  | (coverage_head Bind.bind; apply state_bind)
  | (coverage_head ite; apply state_ite)
  | (coverage_head ForIn.forIn; first | apply state_forIn | apply state_range)
  | maintenance_intro
  | coverage_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

macro "coverage_product_step" : tactic => `(tactic| first
  | (coverage_head liftPrefix; exact product_lift _)
  | (coverage_head liftWGPrefix; exact product_state _ (state_lift _))
  | (coverage_head Pure.pure; exact product_pure _)
  | (coverage_head Bind.bind; apply product_bind)
  | (coverage_head ite; apply product_ite)
  | (coverage_head ForIn.forIn; first | apply product_forIn | apply product_range)
  | maintenance_intro
  | coverage_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars)
  | simp +failIfUnchanged only [bind_assoc,pure_bind])

end Leanux.Proofs.WG.AuthenticatedEffects.CausalJournal.Coverage
