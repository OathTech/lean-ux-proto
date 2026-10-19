import Leanux.Proofs.WG.Progress.CurveEvaluationSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress
open Leanux.WG

/-- A finite evaluator of the original X25519 reference. The ladder is the
existing exact 255-step source factor; inversion uses a bounded recursion,
including its final zero-exponent test. Exhaustion remains explicit. -/
def x25519Finite (k u : Key) : Option Key :=
  let ladder := x25519Ladder k u
  (powEval p25519 ((p25519 - 2) + 1)
    (1, ladder.2 % p25519, p25519 - 2)).map fun final =>
      toLE (ladder.1 * final.1 % p25519)

/-- The original curve wrapper's bytes and nonzero test, evaluated finitely. -/
def curve25519Finite (secret point : Key) : Option (Key × Bool) :=
  (x25519Finite secret point).map fun out => (out, out != nullPoint)

/-- Every input has a completed inversion evaluation; neither curve validity
nor a successful-evaluation hypothesis is assumed. -/
theorem x25519_inversion_finite (k u : Key) :
    ∃ final, powEval p25519 ((p25519 - 2) + 1)
        (1, (x25519Ladder k u).2 % p25519, p25519 - 2) = some final ∧
      final.2.2 = 0 ∧
      x25519 k u = toLE ((x25519Ladder k u).1 * final.1 % p25519) := by
  obtain ⟨final, evaluated, stopped, _⟩ :=
    powMod_finite (x25519Ladder k u).2 (p25519 - 2) p25519
  exact ⟨final, evaluated, stopped, x25519_of_evaluation k u _ final evaluated⟩

/-- Exact original-source equality for arbitrary byte-list inputs, preserving
the original clamping, point decoding and 32-byte output encoding. -/
theorem x25519Finite_source (k u : Key) :
    x25519Finite k u = some (x25519 k u) := by
  obtain ⟨final, evaluated, _, same⟩ := x25519_inversion_finite k u
  dsimp only [x25519Finite]
  rw [evaluated]
  simp only [Option.map_some, same]

/-- The finite wrapper produces exactly the actual bytes and null-point Bool. -/
theorem curve25519Finite_source (secret point : Key) :
    curve25519Finite secret point = some (curve25519 secret point) := by
  unfold curve25519Finite
  rw [x25519Finite_source]
  rfl

end Leanux.Proofs.WG.Progress
