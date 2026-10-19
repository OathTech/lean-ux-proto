import Leanux.Proofs.WG.Progress.KeyConfigurationFiniteSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.KeyConfigurationFinite
open Leanux Leanux.WG

/-- Every original installation outcome agrees, without identity, peer-list,
residency, or successful-evaluation assumptions. -/
theorem original_install_finite (key : Key) :
    Campaign2.AgreesOn (fun _ => True) (Config.keyInstallSource key) (install key) := by
  rw [install_source]
  intro g ambient pre
  rfl

/-- Exact collision/removal evaluation, including original errno and Stop
paths and queued workers encountered during the real removal. -/
theorem original_collision_finite (key : Key) :
    Campaign2.AgreesOn (fun _ => True) (Config.keyCollisionSource key) (collision key) := by
  rw [collision_source]
  intro g ambient pre
  rfl

/-- The native key-stage cut agrees on all entries and arbitrary attributes.
This is the complete private-key stage, not the whole device request or a
successful-completion/fuel-adequacy claim. -/
theorem original_key_stage_finite (attrs : DeviceAttrs) :
    Campaign2.AgreesOn (fun _ => True) (Config.RequestOrder.keyStage attrs) (stage attrs) := by
  rw [stage_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.KeyConfigurationFinite
