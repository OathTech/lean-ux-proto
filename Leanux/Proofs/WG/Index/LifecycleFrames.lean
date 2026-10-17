import Leanux.Proofs.WG.Config.Returns

/-! The device projection survives retirement of dispatch identities. This
within-WireGuard frame is separate from the lifecycle's table claims. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem retireDeviceUnits_device (device : Option Device) :
    ⦃fun w => ⌜w.dev = device⌝⦄ retireDeviceUnits
      ⦃⇓? _ w => ⌜w.dev = device⌝⦄ := by
  apply (ensures_iff _ _ _).mp
  intro g ambient result final after pre run
  simp [retireDeviceUnits, modifyAmbient] at run
  rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
  exact pre

end Leanux.Proofs.WG.Index
