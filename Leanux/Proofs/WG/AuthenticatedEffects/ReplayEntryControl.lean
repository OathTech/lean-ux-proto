import Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntryQuiet

/-! Source-control rules for the counter-entry carrier. Compiler-generated
continuations are shared; every generated term is kernel checked. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Keypairs Keypairs.WGFrames Keypairs.WGTransitions Keypairs.WGMore Keypairs.WGConfig Keypairs.Observers

theorem product_store (h : List Event) (w v : World)
    (same : productStoreView v = productStoreView w) (hi : Inv w.wg ∧ Safe h) : Inv v.wg ∧ Safe h := by
  have snap := congrArg (fun s : ProductStore43 => Keypairs.snapshotOfWGStoreView s.2.2.2) same
  change snapshot v.wg = snapshot w.wg at snap
  exact ⟨by simpa only [Inv,snap] using hi.1,hi.2⟩

theorem product_ite (p : Prop) [Decidable p] {a b : PrefixM Event α}
    (ha : p → ProductSafe a) (hb : ¬p → ProductSafe b) :
    ProductSafe (if p then a else b) := PrefixPreserves.ite p ha hb

theorem product_forIn (xs : List α) (init : β) (f : α → β → PrefixM Event (ForInStep β))
    (safe : ∀ x b, ProductSafe (f x b)) : ProductSafe (forIn xs init f) := by
  induction xs generalizing init with
  | nil => exact product_pure init
  | cons x xs ih =>
    rw [List.forIn_cons]
    apply product_bind (safe x init)
    intro step
    cases step with
    | done b => exact product_pure b
    | yield b => exact ih b

theorem product_range (r : Std.Legacy.Range) (init : β)
    (f : Nat → β → PrefixM Event (ForInStep β)) (safe : ∀ x b, ProductSafe (f x b)) :
    ProductSafe (forIn r init f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact product_forIn _ _ _ safe

open Lean Meta Elab Tactic in
elab "replay_entry_head " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do
    throwError "not a carrier contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back!.consumeMData else action
  let .const actual _ := action.getAppFn | throwError "not a constant-headed source"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different source head"

open Lean Meta Elab Tactic in
elab "replay_entry_native " wanted:ident : tactic => withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).consumeMData
  unless target.isAppOf ``StateSafe do throwError "not a native carrier contract"
  let action := target.getAppArgs.back!.consumeMData.headBeta
  unless action.isAppOf ``liftWGPrefix do throwError "not a native WG lift"
  let native := action.getAppArgs.back!.consumeMData.headBeta
  let .const actual _ := native.getAppFn | throwError "not a native constant"
  let expected := wanted.getId.eraseMacroScopes.toString
  unless actual.toString == expected || actual.toString.endsWith ("." ++ expected) do
    throwError "different native head"

open Lean Meta Elab Tactic in
elab "replay_entry_reduce" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do
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

elab "replay_entry_join_let" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  unless target.isAppOf ``StateSafe || target.isAppOf ``ProductSafe do Lean.throwError "not a carrier contract"
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
    Lean.Meta.withLocalDeclD `replay_entry_join contract fun hf => do
      let next ← Lean.Meta.mkFreshExprSyntheticOpaqueMVar (property (body.instantiate1 fn))
      let proof ← Lean.Meta.mkLambdaFVars #[fn, hf] next
      pure (proof, next.mvarId!)
  goal.assign (Lean.mkApp2 continuation value valueProof)
  Lean.Elab.Tactic.replaceMainGoal [valueProof.mvarId!, next]

elab "replay_entry_join_use" : tactic => Lean.Elab.Tactic.withMainContext do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
  let args := target.getAppArgs
  unless args.size ≥ 2 do Lean.throwError "missing action"
  let action := args.back!.consumeMData
  let action := if action.isAppOf ``liftWGObserver then action.getAppArgs.back! else action
  unless action.getAppFn.isFVar do Lean.throwError "not a local continuation"
  for decl in ← Lean.getLCtx do
    if decl.userName == `replay_entry_join then
      let proof := Lean.mkAppN decl.toExpr action.getAppArgs
      if ← Lean.Meta.withReducible (Lean.Meta.isDefEq (← Lean.Meta.inferType proof) target) then
        goal.assign proof
        Lean.Elab.Tactic.replaceMainGoal []
        return
  Lean.throwError "no continuation contract"

macro "replay_entry_product_step" : tactic => `(tactic| first
  | (replay_entry_head Pure.pure; exact product_pure _)
  | (replay_entry_head ForIn.forIn; first | apply product_forIn | apply product_range)
  | (replay_entry_head Bind.bind; apply product_bind)
  | (replay_entry_head ite; apply product_ite)
  | replay_entry_join_let
  | replay_entry_join_use
  | maintenance_intro
  | replay_entry_reduce
  | (split; all_goals try simp_all only []; all_goals try subst_vars))

macro "replay_entry_native_step" : tactic => `(tactic|
  (replay_entry_head liftWGPrefix
   apply product_state
   apply state_native
   repeat' first | observer_ordinary_leaf | ordinary_strict_step))

end Leanux.Proofs.WG.AuthenticatedEffects.ReplayEntry
