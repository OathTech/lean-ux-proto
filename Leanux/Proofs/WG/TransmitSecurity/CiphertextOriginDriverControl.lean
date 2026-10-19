import Leanux.Proofs.WG.TransmitSecurity.CiphertextOriginDriverWorkers

/-! Share native compiler join continuations without expanding the resident
packet carrier or duplicating a checked suffix proof. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.Proofs.Logged

open Lean Meta Elab Tactic in
elab "ciphertext_carrier_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StatePrefixPreserves || target.isAppOf ``PrefixPreserves do
    throwError "not a carrier contract"
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

elab "ciphertext_carrier_join_let" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StatePrefixPreserves || target.isAppOf ``PrefixPreserves do Lean.throwError "not a carrier contract"
  let .app front observed := target | Lean.throwError "missing action"
  let isProduct := observed.isAppOf ``liftWGObserver
  let action := if isProduct then observed.getAppArgs.back! else observed
  let wrap (a : Lean.Expr) :=
    if isProduct then
      match observed with
      | .app outer _ => Lean.mkApp outer a
      | _ => a
    else a
  let .letE name ty value body _ := action.consumeMData | Lean.throwError "not a let"
  unless name.toString.startsWith "__do_jp" do Lean.throwError "not a join"
  let property (a : Lean.Expr) := Lean.mkApp front (wrap a)
  let valueContract ← Lean.Meta.forallTelescope ty fun args _ => do
    Lean.Meta.mkForallFVars args (property (Lean.mkAppN value args))
  let valueProof ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar valueContract
  let (continuation, next) ← Lean.Meta.withLocalDeclD name ty fun fn => do
    let contract ← Lean.Meta.forallTelescope ty fun args _ => do
      Lean.Meta.mkForallFVars args (property (Lean.mkAppN fn args))
    Lean.Meta.withLocalDeclD `ciphertext_carrier_join contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 fn))
      let proof ← Lean.Meta.mkLambdaFVars #[fn, hf] next
      pure (proof, next.mvarId!)
  goal.assign (Lean.mkApp2 continuation value valueProof)
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "ciphertext_carrier_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing action"
  let action := args.back!.consumeMData
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back! else action
  unless action.getAppFn.isFVar do Lean.throwError "not a local continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `ciphertext_carrier_join then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no continuation contract"


end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
