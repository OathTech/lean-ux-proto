import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTraffic

/-! Configuration frames keep both peer allocation identity and timestamp.
The allocator frontier is retained even where resident peer fields are masked. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

def configView (w : WGWorld) := (freshnessAt w,w.peerCounter)

theorem same_config {action : WG.M α} (same : SameView configView action)
    (history : List TimestampReceipt) : Framing.Preserves (StateInv history) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b hi run
  have equal := (ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run
  have stamps : freshnessAt v = freshnessAt w := congrArg Prod.fst equal
  have frontier : v.peerCounter = w.peerCounter := congrArg Prod.snd equal
  apply state_retained hi
  · intro pid stamp found
    rw [← stamps]
    exact found
  · rw [frontier]
    exact Nat.le_refl _

theorem aip (a : AipM α) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (liftAip a) := by
  apply hoare_liftAip
  intro w d store hi hd
  apply state_retained hi
  · intro pid stamp found
    simpa only [freshnessAt,hd,Option.bind_some] using found
  · exact Nat.le_refl _

theorem node {action : WG.M α} (same : SameNode action) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) action := by
  apply same_config (same.of_factor (fun s : WGStoreView =>
    ((fun pid => (s.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.latestTimestamp)),s.peerCounter))
    configView ?_) history
  intro w
  unfold configView freshnessAt
  simp only [nodeView,nodeDevice,wgStoreView,Option.bind_map,Function.comp_def]

theorem list_del (id : NodeId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (listDel id) := by
  apply same_config ((AllowedIps.listDel_clearListView id).of_factor
    (fun s : WGStoreView × (PeerId → Option Peer) =>
      ((fun pid => (s.2 pid).map fun p => (p.internalId,p.latestTimestamp)),s.1.peerCounter)) configView ?_) history
  intro w
  unfold configView freshnessAt
  simp only [AllowedIps.clearListView,wgStoreView,
    Option.map_bind,Option.map_map,Function.comp_def]

theorem remove_ips (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (removeByPeer pid) := by
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head listDel; exact list_del _ history)
    | (rx_retention_head AllowedIps.removeNodeBody; exact node (removeNodeBody_sameNode _) history)
    | archive_traffic_step history

theorem free_ips (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) WG.free := by
  apply same_config (action := WG.free) ?_ history
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  have kept := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a result v b rfl run
  have projected := congrArg (fun s : WGStoreView × (PeerId → Option Peer) =>
    ((fun pid => (s.2 pid).map fun p => (p.internalId,p.latestTimestamp)),s.1.peerCounter)) kept
  unfold configView freshnessAt
  simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,
    AllowedIps.resetAllowedips,wgStoreView,Option.map_bind,Option.map_map,Option.bind_map,Function.comp_def] using projected

theorem socket {action : WG.M α} (same : SameSocket action) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) action := by
  apply same_config (same.of_factor (fun s : WGOwnedView =>
    ((fun pid => (s.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.latestTimestamp)),s.peerCounter))
    configView ?_) history
  intro w
  unfold configView freshnessAt
  simp only [socketView,socketDevice,wgOwnedView,wgStoreView,
    Option.bind_map,Function.comp_def]

theorem configuration {action : WG.M α} (same : SameConfiguration action) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) action := by
  apply same_config (same.of_factor (fun s : WGOwnedView =>
    ((fun pid => (s.dev.bind fun d => d.peers[pid]?).map fun p => (p.internalId,p.latestTimestamp)),s.peerCounter))
    configView ?_) history
  intro w
  unfold configView freshnessAt
  simp only [configurationView,configurationDevice,wgOwnedView,wgStoreView,
    Option.bind_map,Function.comp_def]

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
