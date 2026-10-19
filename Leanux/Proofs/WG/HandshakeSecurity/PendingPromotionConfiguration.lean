import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionConfigurationFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity
open Responder.DriverCuts (hooks)

theorem config_quiet (attrs : DeviceAttrs) : LabelsQuiet (Driver.configDevice hooks attrs) :=
  fun initial => Driver.configDevice_history (quiet_hooks initial).actors attrs

theorem config_erases (attrs : DeviceAttrs) :
    ErasesStatePrefix (Driver.configDevice hooks attrs) (wgSetDevice attrs) := by
  apply native_via_nonce (Driver.configDevice_projects native_projection attrs)
    (Driver.configDevice_projects NativeDriver.nonce_projection attrs)
  rw [Driver.nonce_configDevice_eq]
  exact Nonce.configDevice_erases attrs

theorem config_device (quiet : H1PendingQuietFrames) (frames : H1ConfigurationFrames)
    (attrs : DeviceAttrs) : Observed (Driver.configDevice hooks attrs) :=
  quiet_native (config_quiet attrs) (config_erases attrs) (Carrier.config_device quiet frames attrs)

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
