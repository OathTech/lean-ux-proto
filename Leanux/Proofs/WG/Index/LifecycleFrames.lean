import Leanux.Proofs.WG.Config.Returns

/-! The device projection survives retirement of dispatch identities. This
within-WireGuard frame is separate from the lifecycle's table claims. -/
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem retireDeviceUnits_device (device : Option Device) :
    ⦃fun w => ⌜w.k.wg = device⌝⦄ retireDeviceUnits
      ⦃⇓? _ w => ⌜w.k.wg = device⌝⦄ := by
  mvcgen [retireDeviceUnits]

end Leanux.Proofs.WG.Index
