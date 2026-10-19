import Leanux.Proofs.WG.Progress.CurveFiniteSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress
open Leanux.WG

/-- Unconditional completed finite evaluation of the original X25519. This
does not assert cryptographic correctness, nonzero output, or whole-driver
termination. Arbitrary byte lists retain the original reference semantics. -/
theorem original_x25519_finite (k u : Key) :
    x25519Finite k u = some (x25519 k u) :=
  x25519Finite_source k u

/-- Unconditional completed finite evaluation of the actual curve wrapper,
including both possible values of its nonzero result. -/
theorem original_curve25519_finite (secret point : Key) :
    curve25519Finite secret point = some (curve25519 secret point) :=
  curve25519Finite_source secret point

end Leanux.Proofs.WG.Progress
