import Leanux.Proofs.WG.RetirementSecurity.HandshakeQueueMaintenance
import Leanux.Proofs.Framing.WGConfiguration
import Leanux.Proofs.Framing.WGAllowedIpsInsert

/-! Native configuration leaves retain physical handshake-input cells.
Peer/key erasure and native inline flushes remain permitted. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option pp.structureInstances false
set_option maxHeartbeats 600000

theorem precompute_cell (pid : PeerId) : SameView view (precomputeStaticStatic pid) := by
  handshake_cell_source [precomputeStaticStatic] using [requireNotPending_cell]

theorem peer_create_cell (key : Key) (psk : Option Key) : SameView view (peerCreate key psk) := by
  handshake_cell_source [peerCreate,handshakeInit,IndexOwner.setPeerWord,resetLastSentHandshake]
    using [dstCacheReset_cell,precompute_cell,setKeypair_cell]

theorem list_del_cell (id : NodeId) : SameView view (listDel id) := by
  handshake_cell_source [listDel] using []

theorem list_add_cell (pid : PeerId) (id : NodeId) : SameView view (listAddTail pid id) := by
  handshake_cell_source [listAddTail] using []

theorem remove_ips_cell (pid : PeerId) : SameView view (removeByPeer pid) := by
  have node (id : NodeId) : SameView view (AllowedIps.removeNodeBody id) := by
    apply (removeNodeBody_sameNode id).of_factor (fun store : WGStoreView=>store.dev.map fun d=>d.handshakeQueue) view
    intro w
    simp only [view,nodeView,nodeDevice,wgStoreView,Option.map_map,Function.comp_def]
  rw [← AllowedIps.removeByPeerWithStep_eq]
  handshake_cell_source [AllowedIps.removeByPeerWithStep,AllowedIps.removeStep] using [list_del_cell,node]

theorem root_lists_cell (root : NodeId) : SameView view (rootRemovePeerLists root) := by
  handshake_cell_source [rootRemovePeerLists] using [list_del_cell]

theorem free_ips_cell : SameView view WG.free := by
  handshake_cell_source [WG.free] using [root_lists_cell]

theorem add_ips_cell (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView view (add root bits key cidr peer) := by
  simp only [add,commonBits,choose,AipNode.bitAt]
  handshake_cell_source [] using [list_add_cell,list_del_cell]

theorem allowedip_cell (pid : PeerId) (ip : AllowedIpAttrs) : SameView view (setAllowedip pid ip) := by
  handshake_cell_source [setAllowedip,WG.insert,WG.andM,WG.orM] using [add_ips_cell]

theorem make_dead_cell (pid : PeerId) : SameView view (peerMakeDead pid) := by
  handshake_cell_source [peerMakeDead] using [remove_ips_cell]

theorem drain_send_cell (limit : Option PeerId) : SameView view (drainHandshakeSendWq limit) := by
  handshake_cell_source [drainHandshakeSendWq,resolveUnit,peekUnit] using [flushed_send_cell,flushed_clear_cell]

theorem timers_stop_cell (pid : PeerId) : SameView view (timersStop pid) := by
  handshake_cell_source [timersStop] using [delTimer_cell,drain_send_cell]

theorem remove_after_cell (pid : PeerId) : SameView view (peerRemoveAfterDead pid) := by
  handshake_cell_source [peerRemoveAfterDead] using [key_clear_cell,timers_stop_cell,drain_send_cell,peerPut_frame]

theorem remove_peer_cell (peer : Option PeerId) : SameView view (peerRemove peer) := by
  handshake_cell_source [peerRemove] using [make_dead_cell,remove_after_cell]

theorem remove_all_cell : SameView view peerRemoveAll := by
  handshake_cell_source [peerRemoveAll] using [free_ips_cell,make_dead_cell,remove_after_cell]

theorem socket_reinit_cell (v4 v6 : Option Nat) : SameView view (socketReinit v4 v6) := by
  handshake_cell_source [socketReinit,sockFree,iputReport] using []

theorem socket_init_cell (port : Nat) : SameView view (socketInit port) := by
  handshake_cell_source [socketInit,iputReport] using [socket_reinit_cell]

theorem port_cell (port : Nat) : SameView view (setPort port) := by
  handshake_cell_source [setPort] using [clear_endpoint_cell,socket_init_cell]

theorem static_key_cell (key : Key) : SameView view (setStaticIdentityPrivateKey key) := by
  have pub:=fun key=>show SameView view _ from (generatePublic_sameWGWorld key).factor view
  handshake_cell_source [setStaticIdentityPrivateKey] using [requireNotPending_cell,pub]

theorem cookie_keys_cell : SameView view cookiePrecomputeDeviceKeys := by
  handshake_cell_source [cookiePrecomputeDeviceKeys] using []

end Leanux.Proofs.WG.RetirementSecurity.HandshakeLengths
