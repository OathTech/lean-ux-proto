import Leanux.Proofs.WG.Keypairs.OrdinaryRules

/-! Direct composition of exact receive-snapshot preservation. This avoids
expanding unrelated result arithmetic while framing an action. -/

namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Std.Do Leanux.Proofs.Framing

theorem snapshot_pure (x : α) : SameSnapshot (pure x) := SameView.pure snapshot x

theorem snapshot_bind {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    {a : StateT S m α} {f : α → StateT S m β}
    (ha : SameView project a) (hf : ∀ x, SameView project (f x)) :
    SameView project (a >>= f) := ha.bind hf

theorem snapshot_ite {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → Snapshot}
    (p : Prop) [Decidable p] {a b : StateT S m α}
    (ha : p → SameView project a) (hb : ¬p → SameView project b) :
    SameView project (if p then a else b) := by
  by_cases hp : p
  · simpa only [ite_eq_left hp] using ha hp
  · simpa only [ite_eq_right hp] using hb hp

theorem snapshot_modify
    {S : Type} {m : Type → Type} {ps : PostShape}
    [Monad m] [WPMonad m ps] {project : S → WGWorld}
    (f : S → S)
    (hf : ∀ w, (project (f w)).dev = (project w).dev ∧
      (project (f w)).keypairCounter = (project w).keypairCounter) :
    SameView (fun w => snapshot (project w)) (modify f : StateT S m Unit) := by
  intro initial
  apply hoare_modify
  intro w hw
  simpa only [snapshot, (hf w).1, (hf w).2] using hw

elab "snapshot_head " n:ident : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.isAppOf ``SameSnapshot || t.isAppOf ``SameView do Lean.throwError "expected SameSnapshot"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do Lean.throwError "different action head"

macro "snapshot_step" : tactic => `(tactic|
  first
    | contradiction
    | keypairs_intro_forall
    | with_reducible assumption
    | (snapshot_head Pure.pure; exact SameView.pure _ _)
    | (snapshot_head Bind.bind; refine snapshot_bind ?_ ?_)
    | (snapshot_head ite; refine snapshot_ite _ ?_ ?_)
    | (snapshot_head modify; refine snapshot_modify (project := id) _ ?_; intro w; exact ⟨rfl, rfl⟩)
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, List.cons.injEq,
        Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false]))

end Leanux.Proofs.WG.Keypairs
