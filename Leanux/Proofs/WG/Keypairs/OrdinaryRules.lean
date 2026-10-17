import Leanux.Proofs.WG.Keypairs.Frames.Tools
import Lean.Elab.Tactic

/-! Direct composition for callers whose individual actions already frame
the lifetime store. Saved keypair replacements use the stronger WP contracts
in the helper proofs, rather than an unconditional rule for replacement. -/
namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing

theorem ordinary_throw (e : Stop) : OrdinaryAction (throw e : WG.M α) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hr
  cases hr

theorem ordinary_map {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (f : α → β) {a : StateT S m α} (ha : Lifetimes.ProjectedAction project Ordinary a) :
    Lifetimes.ProjectedAction project Ordinary (f <$> a) := by
  simpa only [map_eq_pure_bind] using ordinary_bind ha (fun x => SameView.ordinary (SameView.pure project (f x)))

theorem ordinary_discard {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    {a : StateT S m α} (ha : Lifetimes.ProjectedAction project Ordinary a) : Lifetimes.ProjectedAction project Ordinary (discard a) := by
  unfold Functor.discard
  exact ordinary_map _ ha

theorem ordinary_ite {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (p : Prop) [Decidable p] {a b : StateT S m α}
    (ha : p → Lifetimes.ProjectedAction project Ordinary a) (hb : ¬p → Lifetimes.ProjectedAction project Ordinary b) :
    Lifetimes.ProjectedAction project Ordinary (if p then a else b) := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using ha hp
  · simpa only [ite_eq_right hp] using hb hp

theorem ordinary_forIn {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (xs : List α) (b : β) (f : α → β → StateT S m (ForInStep β))
    (hf : ∀ a b, Lifetimes.ProjectedAction project Ordinary (f a b)) : Lifetimes.ProjectedAction project Ordinary (forIn xs b f) := by
  induction xs generalizing b with
  | nil => simpa only [List.forIn_nil] using SameView.ordinary (SameView.pure project b)
  | cons a xs ih =>
    rw [List.forIn_cons]
    apply ordinary_bind (hf a b)
    intro step
    cases step with
    | done b => exact SameView.ordinary (SameView.pure project b)
    | yield b => exact ih b

theorem ordinary_range {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (r : Std.Legacy.Range) (b : β)
    (f : Nat → β → StateT S m (ForInStep β)) (hf : ∀ a b, Lifetimes.ProjectedAction project Ordinary (f a b)) :
    Lifetimes.ProjectedAction project Ordinary (forIn r b f) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact ordinary_forIn _ b f hf

theorem ordinary_forM {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (xs : List α) (f : α → StateT S m PUnit)
    (hf : ∀ a, Lifetimes.ProjectedAction project Ordinary (f a)) : Lifetimes.ProjectedAction project Ordinary (xs.forM f) := by
  induction xs with
  | nil => simpa only [List.forM_eq_forM, List.forM_nil] using SameView.ordinary (SameView.pure project PUnit.unit)
  | cons a xs ih =>
    simpa only [List.forM_eq_forM, List.forM_cons] using ordinary_bind (hf a) (fun _ => ih)

theorem ordinary_array {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (xs : Array α) (b : β)
    (f : α → β → StateT S m (ForInStep β)) (hf : ∀ a b, Lifetimes.ProjectedAction project Ordinary (f a b)) :
    Lifetimes.ProjectedAction project Ordinary (forIn xs b f) := by
  rw [← Array.forIn_toList]
  exact ordinary_forIn _ b f hf

theorem ordinary_get : OrdinaryAction (get : WG.M WGWorld) := by
  apply (Lifetimes.ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w ambient x w' ambient' hr
  cases hr
  exact .refl _

theorem ordinary_modify {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (f : S → S) (hf : ∀ w, Ordinary (project w) (project (f w))) :
    Lifetimes.ProjectedAction project Ordinary (modify f : StateT S m Unit) := by
  intro initial
  apply hoare_modify
  intro w hw
  rw [← hw]
  exact hf w

theorem ordinary_modifyDev (f : Device → Device)
    (hf : ∀ d, (f d).keypairs = d.keypairs) : OrdinaryAction (modifyDev f) := by
  apply SameView.ordinary
  apply sameSnapshot_of_wp
  intro s
  exact modifyDev_snapshot_spec (fun t => t = s) f hf

theorem ordinary_andM (a b : WG.M Bool) (ha : OrdinaryAction a) (hb : OrdinaryAction b) :
    OrdinaryAction (Leanux.WG.andM a b) := by
  unfold Leanux.WG.andM
  apply ordinary_bind ha
  intro result
  cases result
  · exact ordinary_pure false
  · exact hb

theorem ordinary_orM (a b : WG.M Bool) (ha : OrdinaryAction a) (hb : OrdinaryAction b) :
    OrdinaryAction (Leanux.WG.orM a b) := by
  unfold Leanux.WG.orM
  apply ordinary_bind ha
  intro result
  cases result
  · exact hb
  · exact ordinary_pure true

/-- Introduce only an explicit callback argument, keeping contracts opaque. -/
elab "keypairs_intro_forall" : tactic => do
  unless (← Lean.Elab.Tactic.getMainTarget).isForall do
    Lean.throwError "expected an explicit function argument"
  Lean.Elab.Tactic.evalTactic (← `(tactic| intro a))

/-- Inspect the action head without evaluating the action or its framing predicate. -/
elab "ordinary_head " n:ident : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.isAppOf ``OrdinaryAction ||
      (t.isAppOf ``Lifetimes.ProjectedAction &&
        t.getAppArgs[t.getAppArgs.size - 2]!.isConstOf ``Ordinary) do
    Lean.throwError "expected an OrdinaryAction goal"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do
    Lean.throwError "different action head: {a.getAppFn} versus {name}"

macro "ordinary_step" : tactic => `(tactic|
  first
    | contradiction
    | keypairs_intro_forall
    | with_reducible assumption
    | (ordinary_head Pure.pure; exact ordinary_pure _)
    | (ordinary_head MonadExceptOf.throw; exact ordinary_throw _)
    | (ordinary_head get; exact ordinary_get)
    | (ordinary_head modify; refine ordinary_modify _ ?_; intro w; exact Ordinary.refl _)
    | (ordinary_head Leanux.WG.modifyDev; refine ordinary_modifyDev _ ?_; intro d; rfl)
    | (ordinary_head Leanux.WG.andM; refine ordinary_andM _ _ ?_ ?_)
    | (ordinary_head Leanux.WG.orM; refine ordinary_orM _ _ ?_ ?_)
    | (ordinary_head ite; refine ordinary_ite _ ?_ ?_)
    | (ordinary_head Bind.bind; refine ordinary_bind ?_ ?_)
    | (ordinary_head Functor.discard; refine ordinary_discard ?_)
    | (ordinary_head Functor.map; refine ordinary_map _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_range _ _ _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_forIn _ _ _ ?_)
    | (ordinary_head List.forM; with_reducible refine ordinary_forM _ _ ?_)
    | (ordinary_head ForM.forM; with_reducible refine ordinary_forM _ _ ?_)
    | (ordinary_head ForIn.forIn; with_reducible refine ordinary_array _ _ _ ?_)
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, List.cons.injEq,
        Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false]))

end Leanux.Proofs.WG.Keypairs
