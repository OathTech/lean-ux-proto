import Leanux.Spikes.OrdinaryRules

/-! Direct composition of exact receive-snapshot preservation. This avoids
expanding unrelated result arithmetic while framing an action. -/

namespace Leanux.Spikes.Lifetimes
open Leanux Leanux.WG

theorem snapshot_pure (x : α) : SameSnapshot (pure x) := by
  intro w y w' hr
  cases hr
  rfl

theorem snapshot_bind {a : M α} {f : α → M β}
    (ha : SameSnapshot a) (hf : ∀ x, SameSnapshot (f x)) :
    SameSnapshot (a >>= f) := by
  intro w y w' hr
  simp only [StateT.run_bind] at hr
  cases hx : a.run w with
  | error e => simp [hx] at hr
  | ok v =>
    simp only [hx, Leanux.Spikes.Window.except_ok_bind] at hr
    exact (hf v.1 v.2 y w' hr).trans (ha w v.1 v.2 hx)

theorem snapshot_ite (p : Prop) [Decidable p] {a b : M α}
    (ha : p → SameSnapshot a) (hb : ¬p → SameSnapshot b) :
    SameSnapshot (if p then a else b) := by
  by_cases hp : p
  · simpa only [if_pos hp] using ha hp
  · simpa only [if_neg hp] using hb hp

theorem snapshot_modifyK (f : Kernel → Kernel)
    (hf : ∀ k, (f k).wg = k.wg ∧ (f k).keypairCounter = k.keypairCounter) :
    SameSnapshot (modifyK f) := by
  intro w x w' hr
  cases hr
  simp only [snapshot, (hf w.k).1, (hf w.k).2]

elab "snapshot_head " n:ident : tactic => do
  let t := (← Lean.Elab.Tactic.getMainTarget).consumeMData
  unless t.isAppOf ``SameSnapshot do Lean.throwError "expected SameSnapshot"
  let a := t.getAppArgs.back! |>.consumeMData |>.headBeta
  let name ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo n
  unless a.isAppOf name do Lean.throwError "different action head"

macro "snapshot_step" : tactic => `(tactic|
  first
    | contradiction
    | intro_forall
    | with_reducible assumption
    | (snapshot_head Pure.pure; exact snapshot_pure _)
    | (snapshot_head Bind.bind; refine snapshot_bind ?_ ?_)
    | (snapshot_head ite; refine snapshot_ite _ ?_ ?_)
    | (snapshot_head Leanux.modifyK; refine snapshot_modifyK _ ?_; intro k; exact ⟨rfl, rfl⟩)
    | dsimp only
    | (split <;> try simp_all only [Option.some.injEq, List.cons.injEq,
        Prod.mk.injEq, reduceCtorEq, forall_eq', not_true_eq_false]))

end Leanux.Spikes.Lifetimes
