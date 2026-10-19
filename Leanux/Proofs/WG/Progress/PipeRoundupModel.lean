import Leanux.FS.Pipe

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.PipeRoundup

/-- The exact comparison and doubling step of the original Nat helper.
The caller's unsigned-word conversion is outside this helper. -/
def step (target value : Nat) : ForInStep Nat :=
  if value < target then .yield (2 * value) else .done value

/-- Fuel counts encounters, including the final stopping comparison.
Exhaustion is explicit. -/
def evaluate (target : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, value =>
    match step target value with
    | .done final => some final
    | .yield next => evaluate target fuel next

/-- Concrete finite evaluator for the original helper from its initial one. -/
def finite (target : Nat) : Option Nat := evaluate target (target + 1) 1

end Leanux.Proofs.WG.Progress.PipeRoundup
