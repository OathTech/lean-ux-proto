import Leanux.Proofs.WG.Noise.PendingConfigurationFrames


/-! Original allowed-IP insertion preserves the pending ticket view.
The proof uses the existing add source factors, with a single projection
through the AipStore adapter; no trie algorithm is unfolded. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingTickets
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Std.Do Queues

theorem frame_aip {α : Type} (a : AipM α) : SameView view (liftAip a) := by
  intro initial
  apply hoare_liftAip
  intro w d store hi hd
  simpa only [view,hd,Option.bind_some,pending] using hi

theorem listAddTail_frame (pid : PeerId) (id : NodeId) :
    SameView view (listAddTail pid id) :=
  modifyPeer_spec_pending_variant pid
    (fun p => {p with allowedipsList := p.allowedipsList ++ [id]}) (fun _ => rfl)

macro "pending_allowed_step " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from AipM
     exact (frame_aip _).wp (fun s => s = $initial))
  | (rx_retention_head liftAip; exact (frame_aip _).wp (fun s => s = $initial))
  | (rx_retention_head listDel; exact (listDel_frame _).wp (fun s => s = $initial))
  | (rx_retention_head listAddTail; exact (listAddTail_frame _ _).wp (fun s => s = $initial))
  | (rx_retention_head modifyDev
     apply SameView.wp (modifyDev_frame _ ?_ ?_) (fun s => s = $initial)
     all_goals intro d; rfl)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | rx_retention_step)

theorem addPlacedSource_frame (root : Slot) (bits key cidr : Nat) (pid : PeerId)
    (placed : Option NodeId) (exact : Bool) :
    SameView view (Config.addPlacedSource root bits key cidr pid placed exact) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold Config.addPlacedSource Config.addPlacedSourceWith
  repeat' pending_allowed_step initial

theorem addRootSource_frame (root : Slot) (bits key cidr : Nat) (pid : PeerId)
    (trie : Option NodeId) :
    SameView view (Config.addRootSource root bits key cidr pid trie) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold Config.addRootSource Config.addRootSourceWith
  repeat' first
    | (rx_retention_head Config.addPlacedSourceWith
       exact (addPlacedSource_frame _ _ _ _ _ _ _).wp (fun s => s = initial))
    | pending_allowed_step initial

theorem add_frame (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView view (add root bits key cidr peer) := by
  rw [Config.add_transfer_source]
  intro initial
  change Preserves (fun w => view w = initial) _
  repeat' first
    | (rx_retention_head Config.addRootSource
       exact (addRootSource_frame _ _ _ _ _ _).wp (fun s => s = initial))
    | pending_allowed_step initial

theorem insert_frame (family addr cidr : Nat) (pid : PeerId) :
    SameView view (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact (add_frame _ _ _ _ _).wp (fun s => s = initial))
    | pending_allowed_step initial

theorem setAllowedip_frame (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView view (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold setAllowedip WG.andM WG.orM
  repeat' first
    | (rx_retention_head WG.insert; exact (insert_frame _ _ _ _).wp (fun s => s = initial))
    | pending_allowed_step initial

end Leanux.Proofs.WG.Noise.PendingTickets
