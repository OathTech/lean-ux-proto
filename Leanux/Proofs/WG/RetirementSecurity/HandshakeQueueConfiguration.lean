import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueConfigurationFrames
import Leanux.Proofs.WG.Configuration.AllowedIpSource
import Leanux.Proofs.WG.Configuration.DeviceSource

/-! Whole original peer and device configuration retain all physical
handshake input cells, including errno returns after partial mutation. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Configuration
set_option maxHeartbeats 600000
set_option pp.structureInstances false

theorem peer_finish_cell (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    SameView view (peerTailFinishSource attrs peer pid ret) := by
  handshake_cell_source [peerTailFinishSource,WG.andM]
    using [peerPut_frame,sendKeepalive_cell,sendStagedPackets_cell]

theorem peer_tail_cell (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    SameView view (peerConfigTailSource attrs peer pid) := by
  rw [peerConfigTailSource_factor]
  simp only [peerAllowedIpsSource,peerAllowedIpsWith,monadLift_self]
  handshake_cell_source [] using [peerPut_frame,allowedip_cell,peer_finish_cell]

theorem peer_update_cell (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    SameView view (peerConfigUpdateSource attrs peer flags psk pid) := by
  handshake_cell_source [peerConfigUpdateSource,WG.andM]
    using [peerPut_frame,remove_peer_cell,setPeerEndpoint_cell,remove_ips_cell,peer_tail_cell]

theorem set_peer_cell (attrs : PeerAttrs) : SameView view (setPeerCmd attrs) := by
  rw [← setPeerCmd_source]
  handshake_cell_source [setPeerCmdSource,WG.andM]
    using [peerPut_frame,pubkeyLookup_cell,peer_create_cell,peerGet_frame,peer_update_cell]

theorem device_peers_cell (attrs : DeviceAttrs) : SameView view (devicePeersSource attrs) := by
  handshake_cell_source [devicePeersSource] using [set_peer_cell]

theorem device_key_cell (attrs : DeviceAttrs) : SameView view (deviceKeySource attrs) := by
  have pub:=fun key=>show SameView view _ from (generatePublic_sameWGWorld key).factor view
  handshake_cell_source [deviceKeySource,WG.andM]
    using [pub,pubkeyLookup_cell,peerPut_frame,remove_peer_cell,static_key_cell,cookie_keys_cell,
      precompute_cell,key_expire_cell,sendStagedPackets_cell,device_peers_cell]

theorem device_update_cell (attrs : DeviceAttrs) (flags : UInt32) :
    SameView view (deviceUpdateSource attrs flags) := by
  handshake_cell_source [deviceUpdateSource] using [clear_endpoint_cell,port_cell,remove_all_cell,device_key_cell]

theorem set_device_cell (attrs : DeviceAttrs) : SameView view (wgSetDevice attrs) := by
  rw [← wgSetDevice_source]
  have lookup:=fun ref=>show SameView view _ from (lookupInterface_sameWGWorld ref).factor view
  handshake_cell_source [wgSetDeviceSource,WG.orM] using [lookup,device_update_cell]

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
