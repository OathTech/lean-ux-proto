import Leanux.WG.Curve25519

namespace Leanux.Proofs.WG.Progress

/-- The original accumulator, squared base, and remaining exponent. -/
abbrev PowState := Nat × Nat × Nat

/-- Exact square-and-multiply step, including the unreduced initial accumulator. -/
def powStep (modulus : Nat) (s : PowState) : ForInStep PowState :=
  if s.2.2 > 0 then
    if s.2.2 % 2 == 1 then
      .yield (s.1 * s.2.1 % modulus, s.2.1 * s.2.1 % modulus, s.2.2 / 2)
    else
      .yield (s.1, s.2.1 * s.2.1 % modulus, s.2.2 / 2)
  else .done s

/-- Fuel counts step encounters, including the final zero-exponent test.
Exhaustion is explicit and is never mistaken for a completed result. -/
def powEval (modulus : Nat) : Nat → PowState → Option PowState
  | 0, _ => none
  | fuel + 1, s =>
    match powStep modulus s with
    | .done final => some final
    | .yield next => powEval modulus fuel next

end Leanux.Proofs.WG.Progress
