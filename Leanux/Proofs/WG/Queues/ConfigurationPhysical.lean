import Leanux.Proofs.WG.Queues.HolderStopPhysical
import Leanux.Proofs.WG.Queues.DeviceStages

/-! Exact native receive-ring framing through original peer configuration.
The real nullable ring alternative is retained across creation and deletion
of peers; no packet funding or initialized-ring premise is used by the frame. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.ConfigurationPhysical
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open RxRing Leanux.Proofs.WG.Configuration

private theorem listDel_cell (id : NodeId) : SameView nativeCell (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor
    (fun s : WGStoreView × (PeerId → Option Peer) => s.1.dev.map fun d => (d.ifindex,d.decryptQueue))
    nativeCell (fun w => by simp only [AllowedIps.clearListView,nativeCell,Option.map_map,Function.comp_def])

private theorem node_cell (node : NodeId) : SameView nativeCell (AllowedIps.removeNodeBody node) :=
  (removeNodeBody_sameNode node).of_factor
    (fun s : WGStoreView => s.dev.map fun d => (d.ifindex,d.decryptQueue)) nativeCell
    (fun w => by simp only [nodeView,nodeDevice,wgStoreView,nativeCell,Option.map_map,Function.comp_def])

theorem removeByPeer_cell (pid : PeerId) : SameView nativeCell (removeByPeer pid) := by
  rw [←AllowedIps.removeByPeerWithStep_eq]
  ring_cell_source [AllowedIps.removeByPeerWithStep,AllowedIps.removeStep] using [listDel_cell,node_cell]

theorem free_cell : SameView nativeCell WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  have projected := congrArg
    (fun s : WGStoreView × (PeerId → Option Peer) => s.1.dev.map fun d => (d.ifindex,d.decryptQueue)) kept
  simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
    wgStoreView,nativeCell,Option.map_map,Function.comp_def] using projected

theorem makeDead_cell (pid : PeerId) : SameView nativeCell (peerMakeDead pid) := by
  ring_cell_source [peerMakeDead] using [removeByPeer_cell]

theorem afterDead_cell (pid : PeerId) : SameView nativeCell (peerRemoveAfterDead pid) := by
  ring_cell_source [peerRemoveAfterDead] using
    [HolderStopPhysical.keys_cell,HolderStopPhysical.timers_cell,HolderStopPhysical.drain_cell,peerPut_cell]

theorem remove_cell (peer : Option PeerId) : SameView nativeCell (peerRemove peer) := by
  ring_cell_source [peerRemove] using [makeDead_cell,afterDead_cell]

theorem removeAll_cell : SameView nativeCell peerRemoveAll := by
  ring_cell_source [peerRemoveAll] using [free_cell,makeDead_cell,afterDead_cell]

private theorem precompute_cell (pid : PeerId) : SameView nativeCell (precomputeStaticStatic pid) := by
  ring_cell_source [precomputeStaticStatic] using [requireNotPending_cell]

private theorem init_cell (pid : PeerId) (psk : Option Key) : SameView nativeCell (handshakeInit pid psk) := by
  ring_cell_source [handshakeInit,IndexOwner.setPeerWord] using [precompute_cell,setKeypair_cell]

theorem create_cell (key : Key) (psk : Option Key) : SameView nativeCell (peerCreate key psk) := by
  ring_cell_source [peerCreate] using [dstCacheReset_cell,init_cell,HolderStopPhysical.reset_cell]

private theorem listAddTail_cell (pid : PeerId) (node : NodeId) : SameView nativeCell (listAddTail pid node) := by
  ring_cell_source [listAddTail] using []

private theorem add_cell (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView nativeCell (add root bits key cidr peer) := by
  ring_cell_source [add,commonBits,choose,AipNode.bitAt] using [listAddTail_cell,listDel_cell]

private theorem insert_cell (family addr cidr : Nat) (pid : PeerId) :
    SameView nativeCell (WG.insert family addr cidr pid) := by
  ring_cell_source [WG.insert] using [add_cell]

theorem allowedip_cell (pid : PeerId) (ip : AllowedIpAttrs) : SameView nativeCell (setAllowedip pid ip) := by
  ring_cell_source [setAllowedip] using [insert_cell]

theorem finish_cell (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) (ret : Int) :
    SameView nativeCell (peerTailFinishSource attrs peer pid ret) := by
  ring_cell_source [peerTailFinishSource] using [sendKeepalive_cell,sendStagedPackets_cell,peerPut_cell]

theorem tail_cell (attrs : PeerAttrs) (peer : Option PeerId) (pid : PeerId) :
    SameView nativeCell (peerConfigTailSource attrs peer pid) := by
  rw [peerConfigTailSource_factor]
  unfold peerAllowedIpsSource peerAllowedIpsWith
  simp only [monadLift_self]
  ring_cell_source [] using [allowedip_cell,finish_cell,peerPut_cell]

theorem update_cell (attrs : PeerAttrs) (peer : Option PeerId) (flags : UInt32) (psk : Option Key) (pid : PeerId) :
    SameView nativeCell (peerConfigUpdateSource attrs peer flags psk pid) := by
  ring_cell_source [peerConfigUpdateSource] using [remove_cell,peerPut_cell,setPeerEndpoint_cell,removeByPeer_cell,tail_cell]

/-- The actual complete peer command retains epoch and physical decrypt ring
on every normal success or errno result. -/
theorem command_cell (attrs : PeerAttrs) : SameView nativeCell (setPeerCmd attrs) := by
  rw [←setPeerCmd_source]
  ring_cell_source [setPeerCmdSource] using [create_cell,update_cell,pubkeyLookup_cell,peerGet_cell,peerPut_cell]

private theorem optional {action : WG.M α} (same : SameView nativeCell action) :
    Preserves HolderDeviceCreate.OptionalPhysical action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  exact HolderStopPhysical.optional_cell hi
    ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run)

theorem command_physical (attrs : PeerAttrs) :
    Preserves HolderDeviceCreate.OptionalPhysical (setPeerCmd attrs) := optional (command_cell attrs)

end Leanux.Proofs.WG.Queues.RxCredits.ConfigurationPhysical
