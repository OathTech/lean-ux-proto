import Leanux.Proofs.WG.Noise.FreshInstallSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Noise
open Leanux Leanux.WG

/-- Whole original initiation consumption carries the exact tracked next slot
and cursor, hence the explicit initial bound, through every normal result.
The bound is not a readiness or allocation-lifetime assertion. -/
theorem consumeInitiation_fresh_transport (msg : List UInt8) (tracked : PeerId)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (consumeInitiation msg)
      (fun s => s = entry ∧ FreshNextBound tracked entry)
      (fun _ after => freshInstallView tracked after.wg.device =
        freshInstallView tracked entry.wg.device ∧ FreshNextBound tracked after) := by
  intro g ambient result final after pre run
  have same := consumeInitiation_spec_freshTransport_variant msg tracked g.dev
    g ambient result final after rfl run
  have observed : freshInstallView tracked (Campaign2.snapshot final after).wg.device =
      freshInstallView tracked entry.wg.device := by
    rw [← pre.1]
    exact same
  exact ⟨observed,freshNextBound_of_view tracked entry _ observed pre.2⟩

/-- Original response creation transports the same named next/cursor condition
without assuming successful creation, a fresh draw or any release readiness. -/
theorem createResponse_fresh_transport (pid tracked : PeerId) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (createResponse pid)
      (fun s => s = entry ∧ FreshNextBound tracked entry)
      (fun _ after => freshInstallView tracked after.wg.device =
        freshInstallView tracked entry.wg.device ∧ FreshNextBound tracked after) := by
  intro g ambient result final after pre run
  have same := createResponse_spec_freshTransport_variant pid tracked g.dev
    g ambient result final after rfl run
  have observed : freshInstallView tracked (Campaign2.snapshot final after).wg.device =
      freshInstallView tracked entry.wg.device := by
    rw [← pre.1]
    exact same
  exact ⟨observed,freshNextBound_of_view tracked entry _ observed pre.2⟩


end Leanux.Proofs.WG.Noise
