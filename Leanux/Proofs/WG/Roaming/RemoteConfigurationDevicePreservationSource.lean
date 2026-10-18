import Leanux.Proofs.WG.Roaming.RemoteConfigurationPeerPreservationSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteConfiguration
open Leanux Leanux.WG Noise Lifetimes Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Leanux.Proofs.WG.Configuration RemoteSilent
open RemoteDriver

theorem devicePeers_covered (entry : RemoteMap) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (devicePeers RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) := by
  unfold devicePeers devicePeersWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head command; exact command_covered entry _)
    | configuration_remote_step entry

theorem deviceKey_covered (entry : RemoteMap) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (deviceKey RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) := by
  unfold deviceKey deviceKeyWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head devicePeers; exact devicePeers_covered entry _)
    | (maintenance_lift_action_head generatePublic
       exact lift_frame entry _ ((generatePublic_sameWGWorld _).factor destinationAt))
    | (maintenance_lift_action_head setStaticIdentityPrivateKey
       exact lift_frame entry _ (configuration_frame (setStaticIdentityPrivateKey_sameConfiguration _)))
    | (maintenance_lift_action_head cookiePrecomputeDeviceKeys
       exact lift_frame entry _ (configuration_frame cookiePrecomputeDeviceKeys_sameConfiguration))
    | configuration_remote_step entry

theorem deviceUpdate_covered (entry : RemoteMap) (attrs : DeviceAttrs) (flags : UInt32) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (deviceUpdate RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs flags) := by
  unfold deviceUpdate deviceUpdateWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head deviceKey; exact deviceKey_covered entry _)
    | (maintenance_lift_action_head modifyDev
       exact lift_frame entry _ (modifyDev_remotes _ (fun _=>rfl)))
    | configuration_remote_step entry

theorem setDevice_covered (entry : RemoteMap) (attrs : DeviceAttrs) :
    StatePrefixPreserves (fun h g _=>RemoteDriver.NativeInv entry h g) RemoteDriver.Safe
      (setDevice RemoteDriver.Event.rx rxEvent RemoteDriver.Event.birth RemoteDriver.Event.endpoint attrs) := by
  unfold setDevice setDeviceWith StatePrefixPreserves
  dsimp (config := {zeta:=false}) only []
  repeat' first
    | (maintenance_head deviceUpdate; exact deviceUpdate_covered entry _ _)
    | (maintenance_lift_action_head lookupInterface
       exact lift_frame entry _ ((lookupInterface_sameWGWorld _).factor destinationAt))
    | configuration_remote_step entry

end Leanux.Proofs.WG.Roaming.RemoteConfiguration
