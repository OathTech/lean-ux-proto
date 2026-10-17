import Leanux.Proofs.WG.Noise.Execution
import Init.Internal.Order.While

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Proofs.WG.Noise

/-- The original while shape with a fixed, entry-captured bound. The callback
may change arbitrary state and may return an error. -/
def allocationLoop {σ : Type} (n : Nat) (encounter : StateT σ (Except Stop) Bool)
    (s : Option Bool × Nat) : StateT σ (Except Stop) (Option Bool × Nat) :=
  Lean.Loop.forIn Lean.Loop.mk s fun _ state => do
    if state.2 < n then
      if !(← encounter) then return .done (some false, state.2)
      return .yield (none, state.2 + 1)
    else return .done (none, state.2)

/-- Structural recursion bounds outer calls only. Early false retains the actual
successor state; Stop is propagated unchanged with no invented successor. No
termination assumption about an arbitrary callback follows from its type. -/
def allocationEval {σ : Type} : Nat → (StateT σ (Except Stop) Bool) → Nat →
    StateT σ (Except Stop) (Option Bool × Nat)
  | 0, _, k => pure (none, k)
  | fuel + 1, encounter, k => do
    if !(← encounter) then return (some false, k)
    allocationEval fuel encounter (k + 1)

theorem allocationLoop_unfold {σ : Type} (n : Nat)
    (encounter : StateT σ (Except Stop) Bool) (s : Option Bool × Nat) :
    allocationLoop n encounter s = (do
      if s.2 < n then
        if !(← encounter) then return (some false, s.2)
        allocationLoop n encounter (none, s.2 + 1)
      else return (none, s.2)) := by
  unfold allocationLoop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  split
  · simp only [bind_assoc]
    apply bind_congr
    intro result
    cases result <;> simp
  · rfl

/-- Equality of the complete state/error computations. There are at most n-k
callback invocations, and a false result or error ends them immediately. -/
theorem allocationLoop_finite {σ : Type} (n k : Nat)
    (encounter : StateT σ (Except Stop) Bool) :
    allocationLoop n encounter (none, k) = allocationEval (n - k) encounter k := by
  generalize count : n - k = fuel
  induction fuel generalizing k with
  | zero =>
    rw [allocationLoop_unfold]
    have stop : ¬ k < n := by omega
    simp only [stop, ite_false, allocationEval]
  | succ fuel ih =>
    rw [allocationLoop_unfold]
    have more : k < n := by omega
    simp only [more, ite_true, allocationEval]
    apply bind_congr
    intro ok
    cases ok with
    | false => rfl
    | true =>
      simp only [Bool.not_true, Bool.false_eq_true, ite_false]
      exact ih (k + 1) (by omega)

end Leanux.Proofs.WG.Progress
