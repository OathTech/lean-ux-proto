import Leanux.Proofs.WG.Progress.InitiationFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- The complete original initiation creator agrees on every outcome with its
finite evaluator, including early refusal and malformed/missing-input Stops.
The evaluator uses bounded inversion and the original finite index-search
budget; this is not a successful-service or whole-driver completion claim. -/
theorem original_createInitiation_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.createInitiation pid)
      (createInitiation pid) := by
  rw [createInitiation_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.HandshakeFinite
