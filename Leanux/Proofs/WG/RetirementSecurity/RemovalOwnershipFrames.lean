import Leanux.Proofs.WG.RetirementSecurity.PeerHolderFunding
import Leanux.Proofs.WG.Queues.HolderBaseRetirement

/-! Peer retirement detaches the base reference before clearing key slots.
The original make-dead source only changes publication/routing bookkeeping;
it does not itself remove the peer's actual slot or packet key holders. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits

private def ownershipFromClear (s : WGStoreView × (PeerId → Option Peer)) :=
  ((fun id : KeypairId => (s.1.dev.bind fun d => d.keypairs[id]?).map fun k => (k.internalId,k.refcount)),
   s.1.dev.isSome,(fun pid => (s.2 pid).map peerOwnership),
   (fun id : SkbId => (s.1.dev.bind fun d => d.txSkbs[id]?).map (·.keypair)),
   (fun id : SkbId => (s.1.dev.bind fun d => d.rxSkbs[id]?).map (·.keypair)))

private theorem clear_ownership_factor (w : WGWorld) :
    ownershipFromClear (AllowedIps.clearListView w) = ownershipPointView w := by
  unfold ownershipFromClear AllowedIps.clearListView ownershipPointView
    keyReferenceView ownershipAt peerOwnership slotFields keyAt peerAt packetKeyWords
  simp only [Option.map_map,Option.map_bind,Option.bind_map,Function.comp_def,Option.isSome_map]

private theorem listDel_ownership (id : NodeId) : SameView ownershipPointView (listDel id) :=
  (AllowedIps.listDel_clearListView id).of_factor ownershipFromClear ownershipPointView
    (fun w => (clear_ownership_factor w).symm)

private theorem node_ownership {action : WG.M α} (same : SameNode action) :
    SameView ownershipPointView action :=
  same.of_factor (fun s : WGStoreView => ownershipPointView {dev := s.dev}) _ (fun w => by
    unfold ownershipPointView keyReferenceView ownershipAt peerAt keyAt packetKeyWords
    simp only [nodeView,wgStoreView,nodeDevice,Option.bind_map,Function.comp_def,
      Option.isSome_map])

theorem removeByPeer_ownership (pid : PeerId) :
    SameView ownershipPointView (removeByPeer pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  rw [← AllowedIps.removeByPeerWithStep_eq]
  unfold AllowedIps.removeByPeerWithStep AllowedIps.removeStep
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head listDel; exact (listDel_ownership _).wp (· = initial))
    | (rx_retention_head AllowedIps.removeNodeBody
       exact (node_ownership (removeNodeBody_sameNode _)).wp (· = initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => ownershipPointView w = initial)
       intro x b
       change Preserves (fun w => ownershipPointView w = initial) _)
    | ownership_source_step initial

theorem makeDead_ownership (pid : PeerId) :
    SameView ownershipPointView (peerMakeDead pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact (removeByPeer_ownership _).wp (· = initial))
    | ownership_source_step initial

theorem HolderAccount.make_dead (account : HolderAccount temporary w) (pid : PeerId)
    (a b : Ambient)
    (run : ((peerMakeDead pid).run w).run a = .ok (((),v),b)) : HolderAccount temporary v :=
  account.points ((ProjectedAction.iff_run_ambient _ _ _).mp (makeDead_ownership pid) w a () v b run)

end Leanux.Proofs.WG.RetirementSecurity
