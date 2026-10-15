import Leanux.Proofs.WG.Config.AllowedRemovalConverseSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

theorem source_allowedips_remove_pairs (pid : PeerId) (p : Peer) (d : Device)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Campaign2.Ensures (removeByPeer pid) (fun s => s.wg.device = some d)
      (fun _ s => ∃ final, s.wg.device = some final ∧ NodePairs final ∧
        RemovalEffect d p.allowedipsList final ∧
        (∀ other : PeerId, final.peers[other]? = d.peers[other]?.map (erasePeerList p.allowedipsList)) ∧
        final.peers[pid]? = some (erasePeerList p.allowedipsList p) ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        final.peerAllowedips.seq = d.peerAllowedips.seq + (if p.allowedipsList.isEmpty then 0 else 1) ∧
        ∀ id ∈ p.allowedipsList, nodeOwner final id = none) := by
  intro w result final pre run
  obtain ⟨out, device, steps⟩ := removeByPeer_effect_pairs pid d p resident pairs w result final pre run
  refine ⟨out, device, removalEffect_nodePairs steps pairs, steps, removalEffect_peers steps, ?_,
    erasePeerList_own_empty p, removalEffect_seq steps, ?_⟩
  · simpa [resident] using removalEffect_peers steps pid
  · intro id member
    exact removalEffect_owner_none steps id (Or.inl member)

theorem source_peer_make_dead_pairs (pid : PeerId) (p : Peer) (d : Device)
    (resident : d.peers[pid]? = some p) (pairs : NodePairs d) :
    Campaign2.Ensures (peerMakeDead pid) (fun s => s.wg.device = some d)
      (fun _ s => ∃ removed, RemovalEffect (unlistPeer d pid) p.allowedipsList removed ∧
        let final := deadPeerDevice removed pid p
        s.wg.device = some final ∧ NodePairs final ∧
        final.peerList = d.peerList.filter (· != pid) ∧
        final.peerHashtable = d.peerHashtable.filter (·.2 != pid) ∧
        final.indexTable = d.indexTable ∧ final.numPeers = d.numPeers ∧
        final.peers[pid]? = some { erasePeerList p.allowedipsList p with isDead := true } ∧
        (erasePeerList p.allowedipsList p).allowedipsList = [] ∧
        (erasePeerList p.allowedipsList p).refcount = p.refcount ∧
        ∀ id ∈ p.allowedipsList, nodeOwner final id = none) := by
  intro w result final pre run
  obtain ⟨removed, steps, device⟩ := peerMakeDead_effect_pairs pid d p resident pairs w result final pre run
  refine ⟨removed, steps, device, ?_, deadPeerDevice_effects pid p d removed steps⟩
  have shape : NodePairs removed := removalEffect_nodePairs steps (show NodePairs (unlistPeer d pid) from pairs)
  exact shape

end Leanux.Proofs.WG.Config
