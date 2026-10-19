import Leanux.Proofs.WG.Roaming.RemoteConfigurationPreservationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration RemoteSilent
open RemoteDriver

theorem update_covered (entry : RemoteMap) (attrs : PeerAttrs) (peer : Option PeerId)
    (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (update RemoteDriver.Event.rx rxEvent RemoteDriver.Event.endpoint attrs peer flags psk pid) :=
  Invariant.update_preserves (invariant_contracts entry) attrs peer flags psk pid

theorem acquired_covered (entry : RemoteMap) (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (acquired RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint
        attrs key psk flags peer) :=
  Invariant.acquired_preserves (invariant_contracts entry) attrs key psk flags peer

theorem command_covered (entry : RemoteMap) (attrs : PeerAttrs) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (command RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) :=
  Invariant.command_preserves (invariant_contracts entry) attrs

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
