import Leanux.Proofs.WG.Progress.PipeRoundupModel
import Init.Internal.Order.While

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.PipeRoundup
open Leanux

/-- Proof-side view of the original loop, with arbitrary current accumulator. -/
def loop (target value : Nat) : Nat :=
  Lean.Loop.forIn (m := Id) Lean.Loop.mk value (fun _ value => pure (step target value))

theorem original_source (target : Nat) :
    roundupPowOfTwoUL target = loop target 1 := by
  rfl

theorem loop_unfold (target value : Nat) :
    loop target value =
      match step target value with
      | .done final => final
      | .yield next => loop target next := by
  unfold loop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  cases step target value <;> rfl

/-- Positivity is invariant under doubling. While below target, the Nat
difference strictly decreases; the source has no machine-word accumulator. -/
theorem loop_finite (target fuel value : Nat) (positive : 0 < value)
    (enough : target - value < fuel) :
    evaluate target fuel value = some (loop target value) ∧
      target ≤ loop target value := by
  induction fuel generalizing value with
  | zero => omega
  | succ fuel ih =>
    rw [evaluate, loop_unfold]
    by_cases below : value < target
    · have nextPositive : 0 < 2 * value := by omega
      have smaller : target - 2 * value < fuel := by omega
      simpa only [step, below, ↓reduceIte] using ih (2 * value) nextPositive smaller
    · simp only [step, below, ↓reduceIte]
      exact ⟨True.intro, by omega⟩

/-- The original initial value discharges the positivity premise for every
Nat input, including zero. No evaluation-success premise is supplied. -/
theorem finite_source (target : Nat) :
    finite target = some (roundupPowOfTwoUL target) ∧
      target ≤ roundupPowOfTwoUL target := by
  rw [original_source]
  exact loop_finite target (target + 1) 1 (by omega) (by omega)

end Leanux.Proofs.WG.Progress.PipeRoundup
