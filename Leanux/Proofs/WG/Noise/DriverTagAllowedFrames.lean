import Leanux.Proofs.WG.Noise.DriverTagLeafFrames
import Leanux.Proofs.WG.Noise.PendingAllowedInsertionFrames

/-! Allowed-IP operations project the existing list/node contracts onto tags.
Insertion composes the existing source factors, without a second trie proof. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.DriverTags
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Std.Do Queues

theorem aip_frame {α : Type} (a : AipM α) : SameView tagView (liftAip a) := by
  intro initial
  apply hoare_liftAip
  intro w d store hi hd
  funext pid
  simpa only [tagView,responseTagMap,hd,Option.bind_some] using congrFun hi pid

theorem node_frame {α : Type} {a : WG.M α} (frame : SameNode a) : SameView tagView a := by
  apply frame.of_factor (fun s => responseTagMap s.dev) tagView
  intro g
  change responseTagMap g.dev = responseTagMap (g.dev.map nodeDevice)
  cases g.dev <;> rfl

theorem listDel_frame (id : NodeId) : SameView tagView (listDel id) := by
  apply (AllowedIps.listDel_clearListView id).of_factor
    (fun s => fun pid => (s.2 pid).map Peer.handshakeState) tagView
  intro g
  funext pid
  simp [tagView,responseTagMap,AllowedIps.clearListView,
    Option.map_bind,Option.map_map,Function.comp_def]

theorem free_frame : SameView tagView WG.free := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro g ambient result final after run
  have effect := (hoare_iff_run_ambient _ _ _).mp
    (AllowedIps.free_storeView (wgStoreView g)) g ambient result final after rfl run
  have peers := congrArg (fun s : WGStoreView × (PeerId → Option Peer) =>
    fun pid => (s.2 pid).map Peer.handshakeState) effect
  funext pid
  simpa [tagView,responseTagMap,AllowedIps.clearStoreView,
    AllowedIps.clearStoreProjection,wgStoreView,Option.map_bind,Option.map_map,
    Option.bind_map,Function.comp_def,AllowedIps.resetAllowedips] using congrFun peers pid

theorem listAddTail_frame (pid : PeerId) (id : NodeId) : SameView tagView (listAddTail pid id) :=
  modifyPeer_frame pid (fun p => {p with allowedipsList := p.allowedipsList ++ [id]})
    (fun _ => rfl)

theorem removeByPeer_frame (pid : PeerId) : SameView tagView (removeByPeer pid) := by
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep
  apply (getPeer_frame pid).bind
  intro p
  apply (ambient_frame (AmbientM.branch .removeListEmpty p.allowedipsList.isEmpty)).bind
  intro empty
  cases empty with
  | true => exact SameView.pure tagView ()
  | false =>
    apply (modifyDev_frame
      (fun d => {d with peerAllowedips := {d.peerAllowedips with seq := d.peerAllowedips.seq+1}})
      (fun _ => rfl)).bind
    intro u
    apply (DumpComposition.forIn_sameView p.allowedipsList ()
      (fun id _ => AllowedIps.removeStep id) (fun id _ => ?_)).bind
    · intro u
      exact ambient_frame (AmbientM.branch .removeListIter false)
    · unfold AllowedIps.removeStep
      exact (ambient_frame (AmbientM.branch .removeListIter true)).bind (fun _ =>
        (listDel_frame id).bind (fun _ => node_frame (removeNodeBody_sameNode id)))

macro "tag_allowed_step " initial:term : tactic => `(tactic| first
  | (allocation_release_lift_from AipM
     exact (aip_frame _).wp (fun s => s = $initial))
  | (rx_retention_head liftAip; exact (aip_frame _).wp (fun s => s = $initial))
  | (rx_retention_head listDel; exact (listDel_frame _).wp (fun s => s = $initial))
  | (rx_retention_head listAddTail; exact (listAddTail_frame _ _).wp (fun s => s = $initial))
  | (rx_retention_head modifyDev
     apply SameView.wp (modifyDev_frame _ ?_) (fun s => s = $initial)
     intro d
     funext pid
     rfl)
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
    SameView tagView (Config.addPlacedSource root bits key cidr pid placed exact) := by
  intro initial
  change Preserves (fun w => tagView w = initial) _
  unfold Config.addPlacedSource
  repeat' tag_allowed_step initial

theorem addRootSource_frame (root : Slot) (bits key cidr : Nat) (pid : PeerId)
    (trie : Option NodeId) :
    SameView tagView (Config.addRootSource root bits key cidr pid trie) := by
  intro initial
  change Preserves (fun w => tagView w = initial) _
  unfold Config.addRootSource
  repeat' first
    | (rx_retention_head Config.addPlacedSource
       exact (addPlacedSource_frame _ _ _ _ _ _ _).wp (fun s => s = initial))
    | tag_allowed_step initial

theorem add_frame (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView tagView (add root bits key cidr peer) := by
  rw [Config.add_transfer_source]
  intro initial
  change Preserves (fun w => tagView w = initial) _
  repeat' first
    | (rx_retention_head Config.addRootSource
       exact (addRootSource_frame _ _ _ _ _ _).wp (fun s => s = initial))
    | tag_allowed_step initial

theorem insert_frame (family addr cidr : Nat) (pid : PeerId) :
    SameView tagView (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w => tagView w = initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact (add_frame _ _ _ _ _).wp (fun s => s = initial))
    | tag_allowed_step initial

theorem setAllowedip_frame (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView tagView (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w => tagView w = initial) _
  unfold setAllowedip WG.andM WG.orM
  repeat' first
    | (rx_retention_head WG.insert; exact (insert_frame _ _ _ _).wp (fun s => s = initial))
    | tag_allowed_step initial

end Leanux.Proofs.WG.Noise.DriverTags
