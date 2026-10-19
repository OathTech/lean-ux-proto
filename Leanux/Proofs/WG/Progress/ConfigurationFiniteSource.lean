import Leanux.Proofs.WG.Progress.ConfigurationLeafFiniteSource
import Leanux.Proofs.WG.Progress.PeerCreationFiniteCoreSource
import Leanux.Proofs.WG.Progress.KeyConfigurationFiniteSource
import Leanux.Proofs.WG.Queues.JointDevice

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.ConfigurationFinite
open Leanux Leanux.WG

/-- Original allowed-IP loop, including its early error payment and final
continuation, with finite insertion and keepalive callbacks. -/
def tail (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) : WG.M Int :=
  Configuration.peerAllowedIpsWith (fun d b => branch d b) (allowed pid)
    (fun ret => do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
    attrs (finish attrs peer pid)

theorem tail_source (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    Configuration.peerConfigTailSource attrs peer pid = tail attrs peer pid := by
  rw [Configuration.peerConfigTailSource_factor]
  unfold Configuration.peerAllowedIpsSource tail
  rw [funext (allowed_source pid), funext (finish_source attrs peer pid)]
  rfl

def update (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) : WG.M Int :=
  Configuration.peerConfigUpdateWith (fun {_} a => a) (MaintenanceFinite.remove peer)
    (do let p ← getPeer pid; setPeer pid {p with presharedKey := psk.getD []})
    (removeByPeer pid) (setPeerEndpoint pid)
    (fun ret => do peerPut peer; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
    (tail attrs peer pid) attrs flags psk

theorem update_source (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32)
    (psk : Option Key) (pid : PeerId) :
    Configuration.peerConfigUpdateSource attrs peer flags psk pid =
      update attrs peer flags psk pid := by
  rw [Configuration.peerConfigUpdateSource_factor,
    MaintenanceFinite.remove_source, tail_source]
  rfl

/-- Complete original public peer command. Validation, missing-target exits,
allocation failure and all partially completed update effects are retained. -/
def command (attrs : PeerAttrs) : WG.M Int :=
  Configuration.setPeerCmdWith (fun {_} a => a) pubkeyLookup
    (fun ret => do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
    (Configuration.peerCommandAcquiredWith (fun {_} a => a) PeerFinite.create peerGet
      (fun ret => do peerPut none; _ ← branch .peerZeroPsk attrs.presharedKey.isSome; pure ret)
      (update attrs)) attrs

theorem command_source (attrs : PeerAttrs) :
    WG.setPeerCmd attrs = command attrs := by
  rw [← Configuration.setPeerCmd_source, Configuration.setPeerCmdSource_factor]
  have creates : WG.peerCreate = PeerFinite.create :=
    funext fun key => funext (PeerFinite.create_source key)
  have updates : Configuration.peerConfigUpdateSource attrs = update attrs :=
    funext fun peer => funext fun flags => funext fun psk => funext (update_source attrs peer flags psk)
  rw [creates, updates]
  rfl

def peers (attrs : DeviceAttrs) : WG.M Int :=
  Configuration.devicePeersWith (fun {_} a => a) command attrs

theorem peers_source (attrs : DeviceAttrs) :
    Config.devicePeersSource attrs = peers attrs := by
  change Configuration.devicePeersSource attrs = _
  rw [Configuration.devicePeersSource_factor, funext command_source]
  rfl

/-- Actual private-key guards and continuation, using the already factored
collision and identity/peer installation stages. -/
def key (attrs : DeviceAttrs) : WG.M Int :=
  Config.devicePrivateSourceWith KeyConfigurationFinite.collision
    KeyConfigurationFinite.install (peers attrs) attrs

theorem key_source (attrs : DeviceAttrs) :
    Config.deviceKeySource attrs = key attrs := by
  rw [← Config.devicePrivate_source]
  unfold Config.devicePrivateSource key
  rw [funext KeyConfigurationFinite.collision_source,
    funext KeyConfigurationFinite.install_source, peers_source]

def deviceUpdate (attrs : DeviceAttrs) (flags : UInt32) : WG.M Int :=
  Configuration.deviceUpdateWith (fun {_} a => a) clearPeerEndpointSrc setPort
    MaintenanceFinite.removeAll (key attrs) attrs flags

theorem deviceUpdate_source (attrs : DeviceAttrs) (flags : UInt32) :
    Configuration.deviceUpdateSource attrs flags = deviceUpdate attrs flags := by
  rw [Configuration.deviceUpdateSource_factor, MaintenanceFinite.removeAll_source]
  have hkey : Configuration.deviceKeySource attrs = key attrs := key_source attrs
  rw [hkey]
  rfl

/-- Complete actual device setter on arbitrary attributes/state/records. Port
setup remains native: it has only bounded saved-list work and a single hidden
random-port read. All replacement, key and peer-command callbacks are finite. -/
def device (attrs : DeviceAttrs) : WG.M Int :=
  Configuration.setDeviceWith (fun {_} a => a) (deviceUpdate attrs) attrs

theorem device_source (attrs : DeviceAttrs) :
    WG.wgSetDevice attrs = device attrs := by
  rw [← Configuration.wgSetDevice_source, Configuration.setDeviceSource_factor,
    funext (deviceUpdate_source attrs)]
  rfl

end Leanux.Proofs.WG.Progress.ConfigurationFinite
