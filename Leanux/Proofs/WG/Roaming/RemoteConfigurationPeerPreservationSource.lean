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
      (update RemoteDriver.Event.rx rxEvent RemoteDriver.Event.endpoint attrs peer flags psk pid) := by
  unfold update peerConfigUpdateWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head endpointObserved; exact RemoteDriver.endpoint_covered entry _ _)
    | configuration_remote_step entry

theorem acquired_covered (entry : RemoteMap) (attrs : PeerAttrs) (key : Key) (psk : Option Key)
    (flags : UInt32) (peer : Option PeerId) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (acquired RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint
        attrs key psk flags peer) := by
  unfold acquired peerCommandAcquiredWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head birthObserved; exact RemoteDriver.birth_covered entry _ _)
    | (maintenance_head update; exact update_covered entry _ _ _ _ _)
    | configuration_remote_step entry

theorem command_covered (entry : RemoteMap) (attrs : PeerAttrs) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (command RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) := by
  unfold command setPeerCmdWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head acquired; exact acquired_covered entry _ _ _ _ _)
    | configuration_remote_step entry

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
