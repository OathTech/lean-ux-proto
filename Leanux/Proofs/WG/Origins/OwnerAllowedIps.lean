import Leanux.Proofs.WG.Origins.OwnerControls

/-! Native allowed-IP list/trie updates preserve the receiving-owner carrier.
The actual source branches, allocation refusals and Stops are retained; no
trie well-formedness, resident-peer or reference-count premise is required. -/
namespace Leanux.Proofs.WG.OwnerAllowedIps
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues.RxCredits OwnerBounds OwnerControls

macro "owner_allowedip_step" : tactic => `(tactic| first
  | (allocation_release_head commonBits; unfold commonBits)
  | (allocation_release_head choose; unfold choose)
  | (allocation_release_head AipNode.bitAt; unfold AipNode.bitAt)
  | (allocation_release_head branch; unfold branch)
  | (allocation_release_head branchCmp; unfold branchCmp)
  | (allocation_release_head invariant; unfold invariant)
  | owner_control_step)

private theorem listAddTail_preserves (pid : PeerId) (id : NodeId) :
    Preserves Carrier (listAddTail pid id) := by
  unfold listAddTail
  repeat' owner_control_step

theorem listDel_preserves (id : NodeId) : Preserves Carrier (listDel id) := by
  unfold listDel
  repeat' owner_control_step

private theorem add_preserves (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Preserves Carrier (add root bits key cidr peer) := by
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (allocation_release_head listAddTail; exact listAddTail_preserves _ _)
    | (allocation_release_head listDel; exact listDel_preserves _)
    | owner_allowedip_step

private theorem insert_preserves (family addr cidr : Nat) (pid : PeerId) :
    Preserves Carrier (WG.insert family addr cidr pid) := by
  unfold WG.insert
  repeat' first
    | (allocation_release_head add; exact add_preserves _ _ _ _ _)
    | owner_allowedip_step

theorem setAllowedip_preserves (pid : PeerId) (ip : AllowedIpAttrs) :
    Preserves Carrier (setAllowedip pid ip) := by
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head WG.insert; exact insert_preserves _ _ _ _)
    | owner_allowedip_step

theorem node_preserves {α : Type} (a : WG.M α) (frame : SameNode a) :
    Preserves Carrier a := by
  apply OwnerCompletion.preserves_of_frames a
    (Origins.Retaining.of_view (Origins.Retaining.node_material (project := id) frame))
  · exact frame.of_factor (fun s : WGStoreView => OwnerCompletion.geometry {dev := s.dev})
      _ (fun w => by
        simp only [OwnerCompletion.geometry,rxView,nodeView,wgStoreView,nodeDevice,
          Option.map_map,Option.bind_map,Function.comp_def])
  · apply keyEffects_view (allowed := NoPromotion)
    exact frame.of_factor (fun s : WGStoreView => keyView {dev := s.dev})
      _ (fun w => by
        unfold keyView keyWords currentCells
        simp only [nodeView,wgStoreView,nodeDevice,id,
          Option.map_map,Option.bind_map,Function.comp_def])

theorem removeByPeer_preserves (pid : PeerId) : Preserves Carrier (removeByPeer pid) := by
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head listDel; exact listDel_preserves _)
    | (allocation_release_head AllowedIps.removeNodeBody
       exact node_preserves _ (removeNodeBody_sameNode _))
    | owner_allowedip_step

end Leanux.Proofs.WG.OwnerAllowedIps
