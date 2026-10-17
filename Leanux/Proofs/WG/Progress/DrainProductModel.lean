import Leanux.Proofs.WG.Progress.DrainModel
import Leanux.Proofs.WG.Campaign2.ProductView

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.Product
open Leanux Leanux.WG

/-- The original complete campaign observation, including all fixture data. -/
abbrev DrainOutcome := Except DrainFailure (DrainSuccess × Campaign2.Product.Snapshot)

def drainAttempts : DrainOutcome → Nat
  | .error failed => failed.attempts
  | .ok (success, _) => success.attempts

def eraseDrainOutcome : DrainOutcome → Campaign2.Product.Outcome Unit
  | .error failed => .error failed.error
  | .ok (_, final) => .ok ((), final)

def DrainBounded (upTo : Option PeerId) (count : Nat) (out : DrainOutcome) : Prop :=
  drainAttempts out ≤ count + 1 ∧
  match out with
  | .error failed => failed.origin ≠ .ownBudget
  | .ok (success, final) =>
    match success.reason with
    | .empty => flushQueues final.toSnapshot = some ([], [])
    | .requestedClear pid => upTo = some pid

end Leanux.Proofs.WG.Progress.Product
