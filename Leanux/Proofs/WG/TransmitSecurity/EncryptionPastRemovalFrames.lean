import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastHandshake
import Leanux.Proofs.WG.Queues.TxLiveRemoval

/-! Allowed-IP teardown changes routing ownership without restoring any old
TX alias or resetting the packet/device allocation frontiers. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Removal
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition Keys Socket Maintenance
set_option maxHeartbeats 600000

private def fromStore (s : WGStoreView) : View :=
  ⟨s.netIfindexNext,s.dev.map fun d => ⟨d.ifindex,d.nextSkb,d.encryptQueue.items⟩⟩

theorem list_delete (id : NodeId) : Preserves (Ready past active) (listDel id) := by
  apply ready_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveRemoval.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.list_delete) id)
  exact (AllowedIps.listDel_clearListView id).of_factor
    (fun s : WGStoreView × (PeerId → Option Peer) => fromStore s.1) view
    (fun w => by simp only [fromStore,view,AllowedIps.clearListView,wgStoreView,
      Option.map_map,Function.comp_def])

theorem node_remove (id : NodeId) :
    Preserves (Ready past active) (AllowedIps.removeNodeBody id) := by
  apply ready_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLiveRemoval.«0».Leanux.Proofs.WG.Queues.TxDisposition.LiveFrontier.node_remove) id)
  exact (removeNodeBody_sameNode id).of_factor fromStore view
    (fun w => by simp only [fromStore,view,nodeView,nodeDevice,wgStoreView,
      Option.map_map,Function.comp_def])

theorem free_allowedips : Preserves (Ready past active) WG.free := by
  apply ready_frame LiveFrontier.free_allowedips
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  have fields := congrArg (fun s : WGStoreView × (PeerId → Option Peer) => fromStore s.1) kept
  simpa only [fromStore,view,AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,
    AllowedIps.resetAllowedips,wgStoreView,Option.map_map,Function.comp_def] using fields

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast.Removal
