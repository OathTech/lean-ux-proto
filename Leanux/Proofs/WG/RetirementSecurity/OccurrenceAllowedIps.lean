import Leanux.Proofs.WG.RetirementSecurity.OccurrenceRemovalCore
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint
import Leanux.Proofs.Framing.WGAllowedIps

/-! Native allowed-IP removal retains complete TX packet records and owning
queue contents. The masked node/list views erase only unrelated routing data. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceAllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceStack OccurrenceHandshake

theorem list_delete_wire (id : NodeId) : SameView txCryptWire (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor
    (fun s : WGStoreView × (PeerId → Option Peer) => txCryptWire {dev := s.1.dev}) _
    (fun w => by simp only [AllowedIps.clearListView,txCryptWire,TxRing.nativeCell,
      TxDisposition.txPackets,wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])

theorem list_delete_contents (id : NodeId) : SameView txQueueContents (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor
    (fun s : WGStoreView × (PeerId → Option Peer) => fun pid => ((s.2 pid).map fun p => p.txQueue.all).getD []) _
    (fun w => by funext pid; simp only [AllowedIps.clearListView,txQueueContents,handoffTxView,
      Option.map_bind,Option.map_map,Function.comp_def])

theorem node_wire (action : WG.M α) (same : SameNode action) : SameView txCryptWire action :=
  same.of_factor (fun s : WGStoreView => txCryptWire {dev := s.dev}) _
    (fun w => by simp only [nodeView,nodeDevice,txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,
      wgStoreView,Option.map_map,Option.bind_map,Function.comp_def])

theorem node_contents (action : WG.M α) (same : SameNode action) : SameView txQueueContents action :=
  same.of_factor (fun s : WGStoreView => txQueueContents {dev := s.dev}) _
    (fun w => by funext pid; simp only [nodeView,nodeDevice,txQueueContents,handoffTxView,
      wgStoreView,Option.bind_map,Function.comp_def])

theorem remove_wire (pid : PeerId) : SameView txCryptWire (removeByPeer pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head listDel; exact (list_delete_wire _).wp (· = initial))
    | (rx_retention_head AllowedIps.removeNodeBody; exact (node_wire _ (removeNodeBody_sameNode _)).wp (· = initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | occurrence_handshake_wire initial

theorem remove_contents (pid : PeerId) : SameView txQueueContents (removeByPeer pid) := by
  intro initial
  change Preserves (fun w => txQueueContents w = initial) _
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head listDel; exact (list_delete_contents _).wp (· = initial))
    | (rx_retention_head AllowedIps.removeNodeBody; exact (node_contents _ (removeNodeBody_sameNode _)).wp (· = initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txQueueContents w = initial)
       intro x b
       change Preserves (fun w => txQueueContents w = initial) _)
    | occurrence_handshake_contents initial

theorem remove (pid : PeerId) : Preserves (Ready locals active) (removeByPeer pid) :=
  RxPollOccurrences.join (AllowedIpsCall.erases (.removePeer pid)) (AllowedIpsCall.allocation (.removePeer pid))
    (occurrences_queueContents (remove_wire pid) (remove_contents pid))

theorem free_wire : SameView txCryptWire WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  have fields := congrArg
    (fun s : WGStoreView × (PeerId → Option Peer) => txCryptWire {dev := s.1.dev}) kept
  simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
    txCryptWire,TxRing.nativeCell,TxDisposition.txPackets,wgStoreView,Option.map_map,
    Option.bind_map,Function.comp_def] using fields

theorem free_contents : SameView txQueueContents WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  have fields := congrArg
    (fun s : WGStoreView × (PeerId → Option Peer) => fun pid => ((s.2 pid).map fun p => p.txQueue.all).getD []) kept
  funext pid
  simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
    txQueueContents,handoffTxView,wgStoreView,Option.map_map,Option.bind_map,Option.map_bind,
    Function.comp_def] using congrFun fields pid

theorem free : Preserves (Ready locals active) WG.free :=
  RxPollOccurrences.join (AllowedIpsCall.erases .free) (AllowedIpsCall.allocation .free)
    (occurrences_queueContents free_wire free_contents)

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceAllowedIps
