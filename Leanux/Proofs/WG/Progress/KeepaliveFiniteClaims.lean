import Leanux.Proofs.WG.Progress.KeepaliveFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- Exact finite evaluation of the original keepalive caller for every input
mode, retaining allocation refusal, staging and queued-work effects and Stops. -/
theorem original_keepalive_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendKeepalive pid) (keepalive pid) := by
  rw [keepalive_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.HandshakeFinite
