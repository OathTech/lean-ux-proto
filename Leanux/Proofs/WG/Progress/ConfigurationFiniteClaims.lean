import Leanux.Proofs.WG.Progress.ConfigurationFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.ConfigurationFinite
open Leanux Leanux.WG

/-- Exact original validation/insertion result, including malformed attributes,
allocation refusal, and every indexed Stop. -/
theorem original_allowed_finite (pid : PeerId) (attrs : AllowedIpAttrs) :
    Campaign2.AgreesOn (fun _ => True) (WG.setAllowedip pid attrs) (allowed pid attrs) := by
  rw [allowed_source]
  intro g ambient pre
  rfl

/-- The actual acquired-peer tail has finite evaluation on arbitrary inputs;
its negative allowed-IP cutoff and final caller payment remain exact. -/
theorem original_tail_finite (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (Configuration.peerConfigTailSource attrs peer pid)
      (tail attrs peer pid) := by
  rw [tail_source]
  intro g ambient pre
  rfl

/-- Complete original public peer setter, with all original results, ambient
effects and Stops. No validation, allocation or successful-call premise. -/
theorem original_command_finite (attrs : PeerAttrs) :
    Campaign2.AgreesOn (fun _ => True) (WG.setPeerCmd attrs) (command attrs) := by
  rw [command_source]
  intro g ambient pre
  rfl

/-- Complete original device setter on arbitrary mixed attributes. It retains
the original validation/refusal cutoffs, ordered partial effects and Stops. -/
theorem original_device_finite (attrs : DeviceAttrs) :
    Campaign2.AgreesOn (fun _ => True) (WG.wgSetDevice attrs) (device attrs) := by
  rw [device_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.ConfigurationFinite
