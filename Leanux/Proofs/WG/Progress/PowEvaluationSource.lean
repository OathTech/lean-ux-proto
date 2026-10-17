import Leanux.Proofs.WG.Progress.PowSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress

/-- A successful finite evaluation determines the original loop exactly.
Fuel need not exceed the initial exponent; exhaustion supplies no conclusion. -/
theorem powEval_sound (modulus fuel : Nat) (s final : PowState)
    (evaluated : powEval modulus fuel s = some final) :
    powLoop modulus s = final := by
  induction fuel generalizing s with
  | zero => simp [powEval] at evaluated
  | succ fuel ih =>
    rw [powEval] at evaluated
    rw [powLoop_unfold]
    cases step : powStep modulus s with
    | done stopped =>
      simpa only [step, Option.some.injEq] using evaluated
    | yield next =>
      exact ih next (by simpa only [step] using evaluated)

/-- Any successful finite square-and-multiply evaluation gives the exact
result of the original private modular-power implementation. -/
theorem powMod_of_evaluation (b e modulus fuel : Nat) (final : PowState)
    (evaluated : powEval modulus fuel (1, b % modulus, e) = some final) :
    originalPowMod b e modulus = final.1 := by
  rw [powMod_source, powEval_sound modulus fuel _ final evaluated]

end Leanux.Proofs.WG.Progress
