import Leanux.Proofs.WG.Progress.ObservationFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.ObservationFinite
open Leanux

/-- Finite observation preserves the exact return, JSON, final state and Stop. -/
theorem original_observe_finite :
    Campaign2.Product.AgreesOn (fun _ => True) Env.observe observe := by
  rw [observe_source]
  intro state pre
  rfl

end Leanux.Proofs.WG.Progress.ObservationFinite
