import Leanux.Proofs.WG.Index.HashSlotLookupFrames
import Leanux.Proofs.WG.Index.HashSlotClearEffects
import Leanux.Proofs.WG.Index.PeerReleaseEffects
import Leanux.Proofs.WG.Index.OwnerCoherenceKeypairReleaseFrames
import Leanux.Proofs.WG.Index.PeerRelease
import Leanux.Proofs.WG.Index.PeerReleaseOutcomeModel
import Leanux.Proofs.WG.Noise.ClearSource
import Leanux.Proofs.WG.Config.KeyReferences

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

/-- Decrementing a resident peer leaves its three slots intact. -/
theorem nonlastPeerRelease_hashSlotCoverage (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (notLast : p.refcount ≠ 1)
    (covered : HashSlotCoverage d) :
    HashSlotCoverage (releasedPeerDevice d pid p) := by
  simpa only [releasedPeerDevice,ite_eq_right notLast] using
    hashSlotCoverage_peerWrite d pid p {p with refcount := p.refcount - 1}
      resident rfl covered

/-- If the departing peer has no key slots, coverage rules out every hashed
keypair naming it. Other peers and every key value survive the actual deletion. -/
theorem lastPeerRelease_hashSlotCoverage (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (last : p.refcount = 1)
    (empty : clearKeys p = [none,none,none]) (covered : HashSlotCoverage d) :
    HashSlotCoverage (releasedPeerDevice d pid p) := by
  intro entry member kid owner
  have old : entry ∈ d.indexTable := by
    rw [releasedPeer_table,last,ite_eq_left rfl] at member
    exact (List.mem_filter.mp member).1
  obtain ⟨target,peer,key,found,keyFound,keyPeer,slot⟩ := covered entry old kid owner
  have different : pid ≠ target := by
    intro same
    subst target
    have equal : peer = p := Option.some.inj (found.symm.trans resident)
    subst peer
    simp [empty] at slot
  refine ⟨target,peer,key,?_,?_,keyPeer,slot⟩
  · rw [releasedPeer_other pid target d p different]
    exact found
  · rw [releasedPeer_keypairs]
    exact keyFound

/-- Only a final peer release requires the empty-slot premise. The pure effect
does not assert that queue/timer guards or reference decrement return normally. -/
theorem releasedPeer_hashSlotCoverage (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (empty : p.refcount = 1 → clearKeys p = [none,none,none])
    (covered : HashSlotCoverage d) :
    HashSlotCoverage (releasedPeerDevice d pid p) := by
  by_cases last : p.refcount = 1
  · exact lastPeerRelease_hashSlotCoverage d pid p resident last (empty last) covered
  · exact nonlastPeerRelease_hashSlotCoverage d pid p resident last covered

/-- A key release removes its hash before deletion. A retained hashed key keeps
its owner and slot while only its reference count changes. -/
theorem releasedDevice_hashSlotCoverage (d : Device) (id : KeypairId) (k : Keypair)
    (now : Bool) (resident : d.keypairs[id]? = some k)
    (covered : HashSlotCoverage d) :
    HashSlotCoverage (releasedDevice d id k now) := by
  have peers : (releasedDevice d id k now).peers = d.peers := by
    cases now <;> by_cases last : k.refcount = 1 <;>
      simp [releasedDevice,unhashKeypair,last]
  intro entry member kid owner
  have old : entry ∈ d.indexTable := by
    rw [released_table] at member
    split at member
    · exact (List.mem_filter.mp member).1
    · exact member
  obtain ⟨pid,p,key,found,keyFound,keyPeer,slot⟩ := covered entry old kid owner
  by_cases same : id = kid
  · subst kid
    have notLast : k.refcount ≠ 1 := by
      intro last
      exact released_unhashed d id k now (Or.inr last) entry member owner
    have equal : key = k := Option.some.inj (keyFound.symm.trans resident)
    subst key
    refine ⟨pid,p,{k with refcount := k.refcount - 1},?_,?_,keyPeer,slot⟩
    · rw [peers]
      exact found
    · simpa [notLast] using released_keypair d id k now
  · refine ⟨pid,p,key,?_,?_,keyPeer,slot⟩
    · rw [peers]
      exact found
    · rw [released_other_keypair d id kid k now same]
      exact keyFound

/-- Empty slots discharge the last-reference detachment condition once hashed
handshake ownership is coherent. The peer's own handshake row may remain. -/
theorem emptyPeer_hashSlot_detached (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (coherent : HashedOwnersCoherent d)
    (covered : HashSlotCoverage d) (empty : clearKeys p = [none,none,none]) :
    LastOwnerDetached d pid p := by
  have cover := hashSlotCoverage_lastOwnerCovered d pid p resident coherent covered
  intro last entry member other word
  rcases cover last entry member word with own | ⟨kid,owner,slot⟩
  · exact other own
  · simp [empty] at slot

end Leanux.Proofs.WG.Index
