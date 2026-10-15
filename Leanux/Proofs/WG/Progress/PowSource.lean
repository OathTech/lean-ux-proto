import Leanux.Proofs.WG.Progress.PowModel
import Leanux.Proofs.WG.Noise.Execution
import Init.Internal.Order.While

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress

/-- Proof-side access to the original private declaration, not a replacement. -/
abbrev originalPowMod := noise_const _private.Leanux.WG.Curve25519.«0».Leanux.WG.powMod

def powLoop (modulus : Nat) (s : PowState) : PowState :=
  Lean.Loop.forIn (m := Id) Lean.Loop.mk s (fun _ s => pure (powStep modulus s))

theorem powMod_source (b e modulus : Nat) :
    originalPowMod b e modulus = (powLoop modulus (1, b % modulus, e)).1 := by
  rfl

/-- Stock checked fixed-point unfolding, instantiated with the standard
`LawfulMonad Id` and `Lean.Order.MonadTail Id` instances. No executable oracle
is used; finite iteration is established separately below. -/
theorem powLoop_unfold (modulus : Nat) (s : PowState) :
    powLoop modulus s =
      match powStep modulus s with
      | .done final => final
      | .yield next => powLoop modulus next := by
  unfold powLoop
  rw [Lean.Loop.forIn_eq_of_monadTail]
  cases powStep modulus s <;> rfl

/-- A larger fuel than the remaining exponent always includes the stopping
test. This identifies the value of the original loop with a finite evaluation. -/
theorem powLoop_finite (modulus fuel : Nat) (s : PowState) (enough : s.2.2 < fuel) :
    powEval modulus fuel s = some (powLoop modulus s) ∧
      (powLoop modulus s).2.2 = 0 := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    rw [powEval, powLoop_unfold]
    by_cases positive : s.2.2 > 0
    · have smaller : s.2.2 / 2 < fuel := by omega
      by_cases odd : (s.2.2 % 2 == 1) = true
      · simpa [powStep, positive, odd] using
          ih (s.1 * s.2.1 % modulus, s.2.1 * s.2.1 % modulus, s.2.2 / 2) smaller
      · simpa [powStep, positive, odd] using
          ih (s.1, s.2.1 * s.2.1 % modulus, s.2.2 / 2) smaller
    · simp [powStep, positive]
      omega

theorem powMod_finite_with_fuel (b e modulus fuel : Nat) (enough : e < fuel) :
    ∃ final, powEval modulus fuel (1, b % modulus, e) = some final ∧
      final.2.2 = 0 ∧ originalPowMod b e modulus = final.1 := by
  obtain ⟨evaluation, stopped⟩ := powLoop_finite modulus fuel (1, b % modulus, e) enough
  exact ⟨_, evaluation, stopped, powMod_source b e modulus⟩

/-- An unconditional concrete fuel choice for every original input. -/
theorem powMod_finite (b e modulus : Nat) :
    ∃ final, powEval modulus (e + 1) (1, b % modulus, e) = some final ∧
      final.2.2 = 0 ∧ originalPowMod b e modulus = final.1 :=
  powMod_finite_with_fuel b e modulus (e + 1) (by omega)

end Leanux.Proofs.WG.Progress
