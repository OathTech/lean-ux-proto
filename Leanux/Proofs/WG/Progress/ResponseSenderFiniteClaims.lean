import Leanux.Proofs.WG.Progress.ResponseSenderFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- All-entry finite evaluation of the actual response creator, retaining
every original refusal, write and Stop. No successful curve or record premise. -/
theorem original_createResponse_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.createResponse pid) (createResponse pid) := by
  rw [createResponse_source]
  intro g ambient pre
  rfl

/-- All-entry finite evaluation of the complete response sender, including
its actual session, MAC, timer and socket paths. This does not assert delivery. -/
theorem original_sendResponse_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendHandshakeResponse pid) (sendResponse pid) := by
  rw [sendResponse_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.HandshakeFinite
