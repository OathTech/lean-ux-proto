import Leanux.Proofs.WG.Noise.PendingDeviceConfigurationFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do Queues
open PendingReception

theorem configuration_peers (a : DeviceAttrs) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (Config.devicePeersSource a) := by
  unfold Config.devicePeersSource
  simp (config := {zeta := false}) only [branch]
  repeat' pending_device_config_step seen

theorem configuration_key (a : DeviceAttrs) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (Config.deviceKeySource a) := by
  unfold Config.deviceKeySource WG.andM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Config.devicePeersSource; exact configuration_peers _ seen)
    | pending_device_config_step seen

theorem configuration_update (a : DeviceAttrs) (flags : UInt32) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (Config.deviceUpdateSource a flags) := by
  unfold Config.deviceUpdateSource
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head Config.deviceKeySource; exact configuration_key _ seen)
    | pending_device_config_step seen

/-- Every normal result, including errno returns, retains the configured
identity, nullable-slot invariant and pending allocation-history invariant.
No success or reachable-world premise is introduced. -/
theorem device_configuration (a : DeviceAttrs) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (wgSetDevice a) := by
  rw [← Config.wgSetDevice_source]
  unfold Config.wgSetDeviceSource WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head lookupInterface; exact (lookupInterface_sameWGWorld _).wp (fun w => NativeInv w seen))
    | (rx_retention_head Config.deviceUpdateSource; exact configuration_update _ _ seen)
    | pending_device_config_step seen

end Leanux.Proofs.WG.Noise.PendingSession


namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Logged Queues

theorem peer_configuration_observed (attrs : PeerAttrs) :
    PrefixPreserves StateInv HistorySafe
      (RxHistory.mixed (liftWGObserver (setPeerCmdPrefix attrs))) :=
  lifecycle_observed _ _ (setPeerCmdPrefix_erases attrs) (peer_configuration attrs)

theorem device_configuration_observed (attrs : DeviceAttrs) :
    PrefixPreserves StateInv HistorySafe
      (RxHistory.mixed (liftWGObserver (wgSetDevicePrefix attrs))) :=
  lifecycle_observed _ _ (wgSetDevicePrefix_erases attrs) (device_configuration attrs)

end Leanux.Proofs.WG.Noise.PendingSession
