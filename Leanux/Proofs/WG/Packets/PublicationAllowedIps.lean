import Leanux.Proofs.WG.Packets.PublicationHandshakeReceive
import Leanux.Proofs.WG.Packets.PublicationPeerRemoval
import Leanux.Proofs.WG.Origins.JointOwnerConfiguration

/-! Actual allowed-IP mutations preserve existing encrypted-packet anchors.
The trie and peer lists may change; the packet store, epoch, peer frontier
and immutable peer identity fields are retained without a trie-validity premise. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Configuration
open OwnerCompletion (geometry)

macro "publication_aip_geometry " initial:term : tactic => `(tactic| first
  | (first | allocation_release_lift_from AipM | rx_retention_head liftAip
     apply hoare_liftAip
     intro w d table hi hd
     simpa only [geometry,RxCredits.rxView,hd,Option.map_some,Option.bind_some] using hi)
  | (rx_retention_head commonBits; unfold commonBits)
  | (rx_retention_head choose; unfold choose)
  | (rx_retention_head AipNode.bitAt; unfold AipNode.bitAt)
  | (rx_retention_head branch; unfold branch)
  | (rx_retention_head branchCmp; unfold branchCmp)
  | (rx_retention_head invariant; unfold invariant)
  | completion_step $initial)

private theorem listAddTail_geometry (pid : PeerId) (id : NodeId) :
    SameView geometry (listAddTail pid id) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold listAddTail
  repeat' publication_aip_geometry initial

private theorem add_geometry (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    SameView geometry (add root bits key cidr peer) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold add
  simp (config := {zeta := false}) only [branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head listAddTail; exact (listAddTail_geometry _ _).wp (fun s => s = initial))
    | (rx_retention_head listDel; exact ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationPeerRemoval.«0».Leanux.Proofs.WG.PublicationFrontier.listDel_geometry) _).wp (fun s => s = initial))
    | publication_aip_geometry initial

private theorem insert_geometry (family addr cidr : Nat) (pid : PeerId) :
    SameView geometry (WG.insert family addr cidr pid) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold WG.insert
  repeat' first
    | (rx_retention_head add; exact (add_geometry _ _ _ _ _).wp (fun s => s = initial))
    | publication_aip_geometry initial

private theorem setAllowedip_geometry (pid : PeerId) (ip : AllowedIpAttrs) :
    SameView geometry (setAllowedip pid ip) := by
  intro initial
  change Preserves (fun w => geometry w = initial) _
  unfold setAllowedip WG.andM WG.orM
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.insert; exact (insert_geometry _ _ _ _).wp (fun s => s = initial))
    | publication_aip_geometry initial

theorem setAllowedip_preserves (pid : PeerId) (ip : AllowedIpAttrs)
    (history : List RxHistory.Event) : Preserves (Inv history) (setAllowedip pid ip) :=
  preserves_of_configured _ ((setAllowedip_geometry pid ip).factor Prod.snd)
    (CurrentConfiguration.setAllowedip_view pid ip) history

end Leanux.Proofs.WG.PublicationFrontier
