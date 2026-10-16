import Leanux.Proofs.WG.Keypairs.OrdinaryRules

/-! Direct composition of exact receive-snapshot preservation. This avoids
expanding unrelated result arithmetic while framing an action. -/

namespace Leanux.Proofs.WG.Keypairs
open Leanux Leanux.WG Leanux.Proofs.Framing

theorem snapshot_pure (x : α) : SameSnapshot (pure x) := SameView.pure snapshot x

theorem snapshot_bind {a : WG.M α} {f : α → WG.M β}
    (ha : SameSnapshot a) (hf : ∀ x, SameSnapshot (f x)) :
    SameSnapshot (a >>= f) := ha.bind hf

theorem snapshot_ite (p : Prop) [Decidable p] {a b : WG.M α}
    (ha : p → SameSnapshot a) (hb : ¬p → SameSnapshot b) :
    SameSnapshot (if p then a else b) := by
  by_cases hp : p
  · simpa only [if_pos hp] using ha hp
  · simpa only [if_neg hp] using hb hp

theorem snapshot_modify (f : WGWorld → WGWorld)
    (hf : ∀ w, (f w).dev = w.dev ∧ (f w).keypairCounter = w.keypairCounter) :
    SameSnapshot (modify f) := by
  intro initial
  apply hoare_modify
  intro w hw
  simpa only [snapshot, (hf w).1, (hf w).2] using hw

elab "snapshot_head " n:ident : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.isAppOf ``SameSnapshot do Lean.throwError "expected SameSnapshot"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do Lean.throwError "different action head"

macro "snapshot_step" : tactic => `(tactic|
  first
    | contradiction
    | keypairs_intro_forall
    | with_reducible assumption
    | (snapshot_head Pure.pure; exact snapshot_pure _)
    | (snapshot_head Bind.bind; refine snapshot_bind ?_ ?_)
    | (snapshot_head ite; refine snapshot_ite _ ?_ ?_)
    | (snapshot_head modify; refine snapshot_modify _ ?_; intro w; exact ⟨rfl, rfl⟩)
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, List.cons.injEq,
        Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false]))

end Leanux.Proofs.WG.Keypairs
