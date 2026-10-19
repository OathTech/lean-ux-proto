import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionConfigurationLeaves

/-! Complete native configuration preserves the suspended actors tracked by
TX service. This includes failed peer updates, device-key conflict removal,
and every actual keepalive/staged-send path. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Leanux.Proofs.WG.Configuration

theorem peer_finish (a : PeerAttrs) (owner : Option PeerId) (pid : PeerId) (ret : Int) :
    Keeps (peerTailFinishSource a owner pid ret) := by
  suspension_source [peerTailFinishSource,WG.andM] using
    [device,branch,peer,set_peer,keepalive,staged,peer_put]

theorem peer_tail (a : PeerAttrs) (owner : Option PeerId) (pid : PeerId) :
    Keeps (peerConfigTailSource a owner pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp only [monadLift_self]
  suspension_source [] using [branch,aip_set,peer_finish,peer_put]

theorem peer_update (a : PeerAttrs) (owner : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    Keeps (peerConfigUpdateSource a owner flags psk pid) := by
  suspension_source [peerConfigUpdateSource,WG.andM] using
    [branch,peer_remove,peer_put,peer,set_peer,invariant,endpoint,aip_remove,peer_tail]

theorem set_peer_command (a : PeerAttrs) : Keeps (setPeerCmd a) := by
  rw [←setPeerCmd_source]
  suspension_source [setPeerCmdSource,WG.andM] using
    [branch,invariant,device,pubkey_lookup,peer_create,peer_get,peer_put,peer_update]

theorem device_peers (a : DeviceAttrs) : Keeps (devicePeersSource a) := by
  suspension_source [devicePeersSource] using [branch,set_peer_command]

theorem device_key (a : DeviceAttrs) : Keeps (deviceKeySource a) := by
  suspension_source [deviceKeySource,WG.andM] using
    [branch,invariant,device,public_key,pubkey_lookup,peer_put,peer_remove,static_identity,
      cookie_precompute,precompute,expire_keys,staged,device_peers]

theorem device_update (a : DeviceAttrs) (flags : UInt32) : Keeps (deviceUpdateSource a flags) := by
  suspension_source [deviceUpdateSource] using
    [modify_device,branch,device,clear_endpoint,set_port,peer_remove_all,device_key]

theorem lookup_interface (ref : DeviceRef) : Keeps (lookupInterface ref) := by
  suspension_source [lookupInterface,netDevices,WG.orM] using [branch,invariant]

theorem set_device (a : DeviceAttrs) : Keeps (wgSetDevice a) := by
  rw [←wgSetDevice_source]
  suspension_source [wgSetDeviceSource,WG.orM] using
    [lookup_interface,branch,invariant,device,device_update]

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension

namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem set_device_actor (attrs : DeviceAttrs) :
    Preserves (At (Covered locals crypt) crypt active) (liftWG (wgSetDevice attrs)) :=
  At.native (fun _=>Configuration.set_device attrs) (TxSuspension.set_device attrs)

end Leanux.Proofs.WG.RetirementSecurity.TxWork
