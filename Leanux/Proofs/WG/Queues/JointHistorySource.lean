import Leanux.Proofs.WG.Queues.RxWaitAppends

/-! Source join factoring for unconditional product history contracts.
These tactics construct ordinary proof terms; they do not alter declarations. -/
namespace Leanux.Proofs.Logged
open Leanux

theorem Appends.ite {E α : Type} (p : Prop) [Decidable p]
    {a b : PrefixM E α} (ha : p → Appends a) (hb : ¬p → Appends b) :
    Appends (if p then a else b) := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using ha hp
  · simpa only [ite_eq_right hp] using hb hp

theorem HistoryFrame.ite {E F α : Type} (ρ : E → Option F) (p : Prop) [Decidable p]
    {a b : PrefixM E α} (ha : p → HistoryFrame ρ a) (hb : ¬p → HistoryFrame ρ b) :
    HistoryFrame ρ (if p then a else b) := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using ha hp
  · simpa only [ite_eq_right hp] using hb hp

elab "source_history_join" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Appends || target.isAppOf ``HistoryFrame do Lean.throwError "not a history contract"
  let .app property action := target | Lean.throwError "missing action"
  let .letE name type value body _ := action.consumeMData | Lean.throwError "not an action let"
  unless name.toString.startsWith "__do_jp" do Lean.throwError "not a source join"
  let contract ← Lean.Meta.forallTelescope type fun args _ =>
    Lean.Meta.mkForallFVars args (Lean.mkApp property (Lean.mkAppN value args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar contract
  let (continuation,next) ← Lean.Meta.withLocalDeclD name type fun f => do
    let contract ← Lean.Meta.forallTelescope type fun args _ =>
      Lean.Meta.mkForallFVars args (Lean.mkApp property (Lean.mkAppN f args))
    Lean.Meta.withLocalDeclD `source_history_contract contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (Lean.mkApp property (body.instantiate1 f))
      return (← Lean.Meta.mkLambdaFVars #[f,hf] next,next.mvarId!)
  goal.assign (Lean.mkAppN continuation #[value,valueProof])
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!,next]

elab "source_history_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Appends || target.isAppOf ``HistoryFrame do Lean.throwError "not a history contract"
  let action := target.getAppArgs.back!.consumeMData
  unless action.getAppFn.isFVar do Lean.throwError "not a source continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `source_history_contract then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no matching source continuation contract"

elab "source_history_reduce" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``Appends || target.isAppOf ``HistoryFrame do Lean.throwError "not a history contract"
  let .app property action := target | Lean.throwError "missing action"
  let rec reduce : Nat → Lean.Expr → Lean.Expr
    | 0,e => e
    | n+1,e =>
      let e := e.consumeMData
      match e with
      | .letE name _ value body _ =>
        if name.toString.startsWith "__do_jp" then e else reduce n (body.instantiate1 value)
      | _ =>
        match e.getAppFn.consumeMData with
        | .letE name _ value body _ =>
          if name.toString.startsWith "__do_jp" then e else reduce n (Lean.mkAppN (body.instantiate1 value) e.getAppArgs)
        | .lam .. =>
          let next := e.headBeta
          if Lean.Expr.equal e next then e else reduce n next
        | _ => e
  let next := reduce 64 action
  if Lean.Expr.equal next action then Lean.throwError "unchanged action head"
  Lean.Elab.Tactic.replaceMainGoal [← goal.replaceTargetDefEq (Lean.mkApp property next)]

end Leanux.Proofs.Logged
