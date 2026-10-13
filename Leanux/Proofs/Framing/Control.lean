import Lean
import Leanux.Proofs.Framing.Tools

/-! Share contracts for compiler-generated continuations when a large original
body would otherwise duplicate its verification conditions at every branch. -/
namespace Leanux.Proofs.Framing
open Leanux Std.Do Lean Meta Elab Tactic
variable {α β : Type}

theorem view_throw (e : Stop) : SameWGKernel (throw e : M α) := by
  intro w x w' hr; cases hr

theorem view_ite (p : Prop) [Decidable p] {a b : M α}
    (ha : p → SameWGKernel a) (hb : ¬p → SameWGKernel b) :
    SameWGKernel (if p then a else b) := by
  by_cases h : p
  · simpa only [if_pos h] using ha h
  · simpa only [if_neg h] using hb h

theorem view_forIn (xs : List α) (b : β) (f : α → β → M (ForInStep β))
    (hf : ∀ a b, SameWGKernel (f a b)) : SameWGKernel (forIn xs b f) := by
  apply SameView.of_wp
  intro initial
  exact list_view_spec wgKernelView (fun s => s = initial) xs b f
    (fun a b => (hf a b).wp (fun s => s = initial))

theorem view_range (r : Std.Legacy.Range) (b : β)
    (f : Nat → β → M (ForInStep β)) (hf : ∀ a b, SameWGKernel (f a b)) :
    SameWGKernel (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact view_forIn _ b f hf

theorem view_discard (a : M α) (h : SameWGKernel a) : SameWGKernel (discard a) := by
  apply SameView.of_wp
  intro initial
  exact discard_view_spec wgKernelView (fun s => s = initial) a (h.wp (fun s => s = initial))

theorem view_loop (b : β) (f : Unit → β → M (ForInStep β)) (rank : β → Nat)
    (hf : ∀ b, SameWGKernel (f () b))
    (hp : ∀ b, ⦃⌜True⌝⦄ f () b
      ⦃⇓? r _ => ⌜match r with | .done _ => True | .yield b' => rank b' < rank b⌝⦄) :
    SameWGKernel (forIn Lean.Loop.mk b f) := by
  intro w x w' hr
  letI : Nonempty World := ⟨w⟩
  have go : ∀ n b, rank b = n → ∀ w x w',
      (forIn Lean.Loop.mk b f : M β).run w = .ok (x, w') →
      wgKernelView w' = wgKernelView w := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro b hb w x w' hr
      change (Lean.Loop.forIn Lean.Loop.mk b f).run w = .ok (x, w') at hr
      rw [Lean.Loop.forIn_eq_of_monadTail] at hr
      simp only [StateT.run_bind] at hr
      cases he : (f () b).run w with
      | error e => simp [he] at hr
      | ok out =>
        rcases out with ⟨step, v⟩
        simp only [he, Leanux.Proofs.WG.CounterWindow.except_ok_bind] at hr
        have hv := hf b w step v he
        cases step with
        | done b' =>
          cases hr
          exact hv
        | yield b' =>
          have hd := (hoare_iff_triple _ _ _).mpr (hp b) w (.yield b') v trivial he
          have hlt : rank b' < n := by simpa only [hb] using hd
          exact (ih (rank b') hlt b' rfl v x w' hr).trans hv
  exact go (rank b) b rfl w x w' hr

elab "view_head " n:ident : tactic => do
  let t := (← getMainTarget).consumeMData
  unless (t.isAppOf ``SameWGKernel || t.isAppOf ``SameView) do throwError "expected SameWGKernel"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do throwError "different action head"

private def viewHeadBZ : Nat → Expr → Expr
  | 0, e => e
  | n+1, e =>
    let e := e.consumeMData
    match e with
    | .letE _ _ v b _ => viewHeadBZ n (b.instantiate1 v)
    | _ =>
      match e.getAppFn.consumeMData with
      | .letE _ _ v b _ => viewHeadBZ n (mkAppN (b.instantiate1 v) e.getAppArgs)
      | .lam .. =>
        let e' := e.headBeta
        if Expr.equal e e' then e else viewHeadBZ n e'
      | _ => e

elab "view_head_reduce" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless (t.isAppOf ``SameWGKernel || t.isAppOf ``SameView) do throwError "not SameWGKernel"
  let .app f a := t | throwError "missing action"
  let a' := viewHeadBZ 64 a
  if Expr.equal a a' then throwError "head unchanged"
  replaceMainGoal [← g.replaceTargetDefEq (.app f a')]

elab "view_head_match" : tactic => withMainContext do
  let g ← getMainGoal
  let t := (← instantiateMVars (← g.getType)).consumeMData
  unless (t.isAppOf ``SameWGKernel || t.isAppOf ``SameView) do throwError "not SameWGKernel"
  let a := t.getAppArgs.back! |>.consumeMData
  let some _ ← Lean.Meta.matchMatcherApp? a | throwError "not a top matcher"
  replaceMainGoal (← Lean.Meta.Split.splitMatch g a)


/-- Prove each compiler-generated continuation once, then use its contract. -/
elab "view_join_let" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless (target.isAppOf ``SameWGKernel || target.isAppOf ``SameView) do throwError "not SameWGKernel"
  let action := target.getAppArgs.back! |>.consumeMData
  let .letE name ty value body _ := action | throwError "not a let"
  unless name.toString.startsWith "__do_jp" do throwError "not a join continuation"
  let property ← forallTelescope ty fun args _ => do
    let result ← mkAppM ``SameWGKernel #[mkAppN value args]
    mkForallFVars args result
  let valueProof ← mkFreshExprSyntheticOpaqueMVar property
  let (continuation, next) ← withLocalDeclD name ty fun f => do
    let contract ← forallTelescope ty fun args _ => do
      let result ← mkAppM ``SameWGKernel #[mkAppN f args]
      mkForallFVars args result
    withLocalDeclD `view_join contract fun hf => do
      let bodyProp ← mkAppM ``SameWGKernel #[body.instantiate1 f]
      let next ← mkFreshExprSyntheticOpaqueMVar bodyProp
      let proof ← mkLambdaFVars #[f, hf] next
      pure (proof, next.mvarId!)
  goal.assign (mkApp2 continuation value valueProof)
  replaceMainGoal [valueProof.mvarId!, next]

elab "view_join_use" : tactic => withMainContext do
  let goal ← getMainGoal
  let target := (← instantiateMVars (← goal.getType)).consumeMData
  unless (target.isAppOf ``SameWGKernel || target.isAppOf ``SameView) do throwError "not SameWGKernel"
  let action := target.getAppArgs.back! |>.consumeMData |>.headBeta
  unless action.getAppFn.isFVar do throwError "not a local continuation"
  for decl in ← getLCtx do
    if decl.userName == `view_join then
      let proof := mkAppN decl.toExpr action.getAppArgs
      try
        if ← withReducible (isDefEq (← inferType proof) target) then
          goal.assign proof
          replaceMainGoal []
          return
      catch _ => pure ()
  throwError "no continuation contract"

elab "view_intro" : tactic => do
  unless (← getMainTarget).isForall do throwError "expected explicit forall"
  evalTactic (← `(tactic| intro a))

macro "view_step" : tactic => `(tactic|
  first
    | contradiction
    | view_intro
    | with_reducible assumption
    | view_join_let
    | view_join_use
    | (view_head Pure.pure; exact SameView.pure _ _)
    | (view_head MonadExceptOf.throw; exact view_throw _)
    | (view_head ite; refine view_ite _ ?_ ?_)
    | (view_head Bind.bind; refine SameView.bind ?_ ?_)
    | (view_head Functor.discard; refine view_discard _ ?_)
    | (view_head Functor.map; refine SameView.map ?_ _)
    | (view_head ForIn.forIn; with_reducible refine view_range _ _ _ ?_)
    | (view_head ForIn.forIn; with_reducible refine view_forIn _ _ _ ?_)
    | view_head_reduce
    | view_head_match)

end Leanux.Proofs.Framing
