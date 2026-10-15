import Leanux.Proofs.WG.Config.RemoveAllModel
import Leanux.Proofs.WG.Config.AllowedPairsEffects

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

theorem deadStep_residents (d removed : Device) (pid other : PeerId) (p q : Peer)
    (step : RemovalEffect (unlistPeer d pid) p.allowedipsList removed)
    (selected : d.peers[pid]? = some p) (resident : d.peers[other]? = some q) :
    ∃ next, (deadPeerDevice removed pid p).peers[other]? = some next ∧
      next.isDead = (q.isDead || (other == pid)) := by
  by_cases same : other = pid
  · subst other
    have peers : p = q := Option.some.inj (selected.symm.trans resident)
    subst q
    refine ⟨{ erasePeerList p.allowedipsList p with isDead := true }, ?_, ?_⟩
    · simp [deadPeerDevice, withPeer]
    · simp
  · have peer := removalEffect_peers step other
    have deadness := congrArg Peer.isDead (erasePeerList_exceptList p.allowedipsList q)
    have different : (other == pid) = false := beq_eq_false_iff_ne.mpr same
    refine ⟨erasePeerList p.allowedipsList q, ?_, ?_⟩
    · simpa [deadPeerDevice, withPeer, Std.TreeMap.getElem?_insert, same, Ne.symm same,
        unlistPeer, resident] using peer
    · simpa only [different, Bool.or_false] using deadness

theorem deadStep_nodePairs (d removed : Device) (pid : PeerId) (p : Peer)
    (step : RemovalEffect (unlistPeer d pid) p.allowedipsList removed) (pairs : NodePairs d) :
    NodePairs (deadPeerDevice removed pid p) := by
  have shape : NodePairs removed := removalEffect_nodePairs step (show NodePairs (unlistPeer d pid) from pairs)
  exact shape

end Leanux.Proofs.WG.Config
