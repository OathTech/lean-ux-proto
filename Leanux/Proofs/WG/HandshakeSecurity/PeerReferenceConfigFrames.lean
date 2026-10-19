import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceTraffic

/-! Configuration projections retain positive resident reference counts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem aip (a : AipM α) : Framing.Preserves Inv (liftAip a) := by
  apply hoare_liftAip
  intro w d store hi hd
  simpa only [Inv,Positive,PeerReference.view,hd,Option.bind_some] using hi

theorem node {action : WG.M α} (same : SameNode action) : Framing.Preserves Inv action := by
  apply frame (same.of_factor (fun s : WGStoreView =>
    fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.refcount) view ?_)
  intro w
  unfold PeerReference.view
  simp only [nodeView,nodeDevice,wgStoreView,Option.bind_map,Function.comp_def]

theorem list_del (id : NodeId) : Framing.Preserves Inv (listDel id) := by
  apply frame ((AllowedIps.listDel_clearListView id).of_factor
    (fun s : WGStoreView × (PeerId → Option Peer) => fun pid => (s.2 pid).map Peer.refcount) view ?_)
  intro w
  unfold PeerReference.view
  simp only [AllowedIps.clearListView,wgStoreView,
    Option.map_bind,Option.map_map,Function.comp_def]

theorem remove_ips (pid : PeerId) : Framing.Preserves Inv (removeByPeer pid) := by
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head listDel; exact list_del _)
    | (rx_retention_head AllowedIps.removeNodeBody; exact node (removeNodeBody_sameNode _))
    | peer_reference_traffic_step

theorem free_ips : Framing.Preserves Inv WG.free := by
  apply frame (action := WG.free)
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  have projected := congrArg (fun s : WGStoreView × (PeerId → Option Peer) =>
    fun pid => (s.2 pid).map Peer.refcount) kept
  unfold PeerReference.view
  simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,
    AllowedIps.resetAllowedips,wgStoreView,Option.map_bind,Option.map_map,Option.bind_map,Function.comp_def] using projected

theorem socket {action : WG.M α} (same : SameSocket action) : Framing.Preserves Inv action := by
  apply frame (same.of_factor (fun s : WGOwnedView =>
    fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.refcount) view ?_)
  intro w
  unfold PeerReference.view
  simp only [socketView,socketDevice,wgOwnedView,wgStoreView,Option.bind_map,Function.comp_def]

theorem configuration {action : WG.M α} (same : SameConfiguration action) : Framing.Preserves Inv action := by
  apply frame (same.of_factor (fun s : WGOwnedView =>
    fun pid => (s.dev.bind fun d => d.peers[pid]?).map Peer.refcount) view ?_)
  intro w
  unfold PeerReference.view
  simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
    Option.bind_map,Function.comp_def]

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
