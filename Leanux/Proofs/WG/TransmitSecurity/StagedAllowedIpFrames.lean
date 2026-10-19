import Leanux.Proofs.WG.TransmitSecurity.StagedPeerCreationFrames
import Leanux.Proofs.WG.AllowedIps.ClearEndpoint
import Leanux.Proofs.Framing.WGAllowedIps

/-! Routing-table edits retain staged plaintexts and peer allocation stamps.
Saved peer-list writes use the existing exact list-removal projection. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem aip (action : AipM α) : Preserves (Inv h) (liftAip action) := by
  apply hoare_liftAip
  intro w d table before device
  apply before.retains
  · simp only [Packets.epoch,device,Option.map_some]
  · intro pid cell found
    simpa only [stagedAt,device,Option.bind_some] using found

theorem list_add (pid : PeerId) (node : NodeId) : Preserves (Inv h) (listAddTail pid node) := by
  unfold listAddTail
  exact update_peer _ _ (fun _ => ⟨rfl,rfl⟩)

theorem list_delete (node : NodeId) : Preserves (Inv h) (listDel node) := by
  have same := AllowedIps.listDel_clearListView node
  apply frame
  · exact same.of_factor (fun s => s.1.dev.map Device.ifindex) Packets.epoch
      (fun w => by simp only [AllowedIps.clearListView,Packets.epoch,Option.map_map,Function.comp_def])
  · apply Staged.of_view
    exact same.of_factor (fun s => fun pid => (s.2 pid).map (fun p => (p.internalId,p.staged))) stagedAt
      (fun w => by funext pid; simp only [AllowedIps.clearListView,stagedAt,Option.map_bind,
        Option.map_map,Function.comp_def])

theorem node {action : WG.M α} (same : SameNode action) : Preserves (Inv h) action := by
  apply frame
  · exact same.of_factor (fun s => s.dev.map Device.ifindex) Packets.epoch
      (fun w => by simp only [nodeView,nodeDevice,wgStoreView,Packets.epoch,Option.map_map,Function.comp_def])
  · apply Staged.of_view
    exact same.of_factor (fun s => stagedAt {dev := s.dev}) stagedAt
      (fun w => by funext pid; simp only [nodeView,nodeDevice,wgStoreView,stagedAt,Option.bind_map,Function.comp_def])

macro "staged_aip_native" : tactic => `(tactic| first
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_lift_from AipM; exact aip _)
  | (rx_retention_head liftAip; exact aip _)
  | (rx_retention_head listAddTail; exact list_add _ _)
  | (rx_retention_head listDel; exact list_delete _)
  | staged_origin_native)

theorem allowedip_add (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Preserves (Inv h) (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' staged_aip_native

theorem allowedip_insert (family addr cidr : Nat) (pid : PeerId) :
    Preserves (Inv h) (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact allowedip_add _ _ _ _ _)
    | staged_aip_native

theorem allowedip_set (pid : PeerId) (ip : AllowedIpAttrs) : Preserves (Inv h) (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  repeat' first
    | (rx_retention_head WG.insert; exact allowedip_insert _ _ _ _)
    | staged_aip_native

theorem allowedip_remove (pid : PeerId) : Preserves (Inv h) (removeByPeer pid) := by
  rw [←AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head AllowedIps.removeNodeBody; exact node (removeNodeBody_sameNode _))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv h)
       intro x b
       change Preserves (Inv h) _)
    | staged_aip_native

theorem allowedip_free : Preserves (Inv h) WG.free := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a value v b before run
  have same := (hoare_iff_run_ambient _ _ _).mp (AllowedIps.free_storeView (wgStoreView w))
    w a value v b rfl run
  apply before.retains
  · have epoch := congrArg (fun s : WGStoreView × (PeerId → Option Peer) => s.1.dev.map Device.ifindex) same
    simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
      wgStoreView,Packets.epoch,Option.map_map,Function.comp_def] using epoch
  · have queues := congrArg (fun s : WGStoreView × (PeerId → Option Peer) =>
        fun pid => (s.2 pid).map (fun p => (p.internalId,p.staged))) same
    have retained : stagedAt v = stagedAt w := by
      funext pid
      simpa only [AllowedIps.clearStoreView,AllowedIps.clearStoreProjection,AllowedIps.resetAllowedips,
        stagedAt,wgStoreView,Option.bind_map,Option.map_bind,Option.map_map,Function.comp_def] using congrFun queues pid
    intro pid cell found
    simpa only [retained] using found

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
