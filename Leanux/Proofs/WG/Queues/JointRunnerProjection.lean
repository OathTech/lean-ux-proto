import Leanux.Proofs.WG.Queues.JointRunnerSource

/-! Source composition for the exact typed outer runner projection. Paired
continuations are factored into checked lemmas, retaining all proof obligations. -/
namespace Leanux.Proofs.WG.Queues.RoutingJoint
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged Configuration

elab "joint_outer_head " name:ident : tactic => do
  let ty := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless ty.isAppOf ``ProjectsOuter do Lean.throwError "not an outer projection"
  let args := ty.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing actions"
  let .const actual _ := args[args.size - 2]!.consumeMData.getAppFn
    | Lean.throwError "not a constant action"
  let expected := name.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    Lean.throwError "different action"

elab "joint_outer_join" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ProjectsOuter do Lean.throwError "not a projection"
  let .app (.app front observed) original := target | Lean.throwError "missing actions"
  let .letE oname oty oval obody _ := observed.consumeMData | Lean.throwError "not an observer let"
  let .letE rname rty rval rbody _ := original.consumeMData | Lean.throwError "not a source let"
  unless oname.toString.startsWith "__do_jp" && rname.toString.startsWith "__do_jp" do
    Lean.throwError "not paired joins"
  let property (g a : Lean.Expr) := Lean.mkApp2 front g a
  let valueContract ← Lean.Meta.forallTelescope oty fun args _ => do
    Lean.Meta.mkForallFVars args (property (Lean.mkAppN oval args) (Lean.mkAppN rval args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar valueContract
  let (continuation, next) ← Lean.Meta.withLocalDeclD oname oty fun g => do
    Lean.Meta.withLocalDeclD rname rty fun a => do
      let contract ← Lean.Meta.forallTelescope oty fun args _ => do
        Lean.Meta.mkForallFVars args (property (Lean.mkAppN g args) (Lean.mkAppN a args))
      Lean.Meta.withLocalDeclD `joint_outer_projection_join contract fun hg => do
        let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar
          (property (obody.instantiate1 g) (rbody.instantiate1 a))
        let proof ← Lean.Meta.mkLambdaFVars #[g, a, hg] next
        pure (proof, next.mvarId!)
  goal.assign (Lean.mkAppN continuation #[oval, rval, valueProof])
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "joint_outer_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ProjectsOuter do Lean.throwError "not a projection"
  let args := target.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing actions"
  let observed := args[args.size - 2]!.consumeMData
  let original := args.back!.consumeMData
  unless observed.getAppFn.isFVar && original.getAppFn.isFVar do
    Lean.throwError "not paired local continuations"
  for decl in ← Lean.getLCtx do
    if decl.userName == `joint_outer_projection_join then
      let proof := Lean.mkAppN decl.toExpr observed.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no paired continuation contract"

elab "joint_outer_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``ProjectsOuter do Lean.throwError "not a projection"
  let .app (.app front observed) lower := target | Lean.throwError "missing paired observers"
  let rec head : Nat → Lean.Expr → Lean.Expr
    | 0, e => e
    | n+1, e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else head n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e else head n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. => let next := e.headBeta; if Lean.Expr.equal e next then e else head n next
        | _ => e
  let reduce (a : Lean.Expr) : Lean.MetaM Lean.Expr := do
    let a := head 64 a
    if (← Lean.Meta.matchMatcherApp? a).isSome then
      if let .reduced next ← Lean.Meta.reduceMatcher? a then return next
    return a
  let observed' ← reduce observed
  let lower' ← reduce lower
  if Lean.Expr.equal observed observed' && Lean.Expr.equal lower lower' then
    Lean.throwError "unchanged paired heads"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp2 front observed' lower')]


macro "joint_outer_step" : tactic => `(tactic| first
  | joint_outer_join
  | joint_outer_join_use
  | joint_outer_reduce
  | (joint_outer_head throw; exact projectsOuter_throw _ _ _)
  | (joint_outer_head ite; apply projectsOuter_ite)
  | (joint_outer_head Bind.bind; apply projectsOuter_bind _ id _)
  | (joint_outer_head ForIn.forIn; first | apply projectsOuter_array | apply projectsOuter_forIn)
  | (joint_outer_head Functor.map; simp only [map_eq_pure_bind])
  | maintenance_intro
  | dsimp (config := {failIfUnchanged := true}) only
  | split)

theorem runnerTailWith_projects {E F α β : Type} (ρ : E → Option F) (p : α → β)
    (call : Syscall → PrefixM E Int) (lower : Syscall → PrefixM F Int)
    (finish : Json → World → α) (finishLower : Json → World → β)
    (hc : ∀ c, ProjectsPrefix ρ id (call c) (lower c))
    (hf : ∀ j w, p (finish j w) = finishLower j w) (trace : Trace) (w : World) :
    ProjectsOuter ρ p (runnerTailWith call finish trace w)
      (runnerTailWith lower finishLower trace w) := by
  unfold runnerTailWith
  repeat' first
    | (joint_outer_head Pure.pure; apply projectsOuter_pure_of; first | rfl | exact hf _ _)
    | (joint_outer_head runAtPrefix
       apply projectsOuter_runAt_id
       first | exact hc _ | exact projectsPrefix_lift _ _)
    | joint_outer_step

theorem executeTraceWith_projects {E F α β : Type} (ρ : E → Option F) (p : α → β)
    (call : Syscall → PrefixM E Int) (lower : Syscall → PrefixM F Int)
    (finish : Json → World → α) (finishLower : Json → World → β)
    (hc : ∀ c, ProjectsPrefix ρ id (call c) (lower c))
    (hf : ∀ j w, p (finish j w) = finishLower j w) (trace : Trace) (placeholders : Bool) :
    ProjectsOuter ρ p (executeTraceWith call finish trace placeholders)
      (executeTraceWith lower finishLower trace placeholders) := by
  unfold executeTraceWith
  repeat' first
    | (joint_outer_head runnerTailWith; exact runnerTailWith_projects ρ p call lower finish finishLower hc hf _ _)
    | (joint_outer_head Pure.pure; apply projectsOuter_pure_of; rfl)
    | joint_outer_step

end Leanux.Proofs.WG.Queues.RoutingJoint
