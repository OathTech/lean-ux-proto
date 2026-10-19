import Leanux.Proofs.WG.Roaming.RemoteConfigurationPeerPreservationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration RemoteSilent
open RemoteDriver

theorem devicePeers_covered (entry : RemoteMap) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (devicePeers RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) :=
  Invariant.devicePeers_preserves (invariant_contracts entry) attrs

theorem deviceKey_covered (entry : RemoteMap) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (deviceKey RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) :=
  Invariant.deviceKey_preserves (invariant_contracts entry) attrs

theorem deviceUpdate_covered (entry : RemoteMap) (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (deviceUpdate RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs flags) :=
  Invariant.deviceUpdate_preserves (invariant_contracts entry) attrs flags

theorem setDevice_covered (entry : RemoteMap) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (setDevice RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) :=
  Invariant.setDevice_preserves (invariant_contracts entry) attrs

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
