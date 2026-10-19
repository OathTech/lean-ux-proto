import Leanux.Proofs.WG.Progress.ConsumerFiniteSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.ConsumerFinite
open Leanux Leanux.WG
/-- Exact finite counterpart of the complete original initiation consumer,
for every entry and input mode, including original refusal and Stop outcomes. -/
theorem original_initiation_finite (msg : List UInt8) :
    Campaign2.AgreesOn (fun _ => True) (consumeInitiation msg) (initiation msg) := by
  rw [initiation_source]
  intro g ambient pre
  rfl
/-- Exact finite counterpart of the complete original response consumer,
including lookup errors, both DH refusals, authentication and payment Stops. -/
theorem original_response_finite (msg : List UInt8) :
    Campaign2.AgreesOn (fun _ => True) (consumeResponse msg) (response msg) := by
  rw [response_source]
  intro g ambient pre
  rfl
end Leanux.Proofs.WG.Progress.ConsumerFinite
