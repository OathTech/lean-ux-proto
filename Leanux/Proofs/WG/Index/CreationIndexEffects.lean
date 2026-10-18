import Leanux.Proofs.WG.Index.OwnerCoherencePeerCreateClaims
import Leanux.Proofs.WG.Index.HashSlotModel
import Leanux.Proofs.WG.Index.RetirementModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise Leanux.Proofs.Framing Lifetimes
open Queues.RxCredits

/-- At a vacant allocation slot, the existing exact footprint preserves every
hashed key's original resident owner and its actual key slot. -/
theorem peerCreateFootprint_hashSlots (before after : Device) (pid : PeerId)
    (footprint : PeerCreateFootprint before after pid)
    (vacant : before.peers[pid]? = none) (covered : HashSlotCoverage before) :
    HashSlotCoverage after := by
  intro entry member kid owner
  obtain ⟨target,p,key,resident,keyFound,word,slot⟩ :=
    covered entry (footprint.1 ▸ member) kid owner
  have different : target ≠ pid := by
    intro same
    subst target
    rw [vacant] at resident
    cases resident
  exact ⟨target,p,key,(footprint.2.2 target different).trans resident,
    by simpa only [footprint.2.1] using keyFound,word,slot⟩

/-- Initial coverage excludes any old hashed key owned by the vacant target.
Thus every final hashed dead owner is an unchanged old peer, even without
observing the newborn's dead flag or requiring a new retirement occurrence. -/
theorem peerCreateFootprint_retirement (before after : Device) (pid : PeerId)
    (footprint : PeerCreateFootprint before after pid)
    (vacant : before.peers[pid]? = none) (epoch : after.ifindex = before.ifindex)
    (covered : HashSlotCoverage before) (retired : Reservations)
    (reserved : DeadHashedReserved retired before) : DeadHashedReserved retired after := by
  intro entry member kid key target p owner keyFound word resident dead
  have oldMember : entry ∈ before.indexTable := footprint.1 ▸ member
  have oldKey : before.keypairs[kid]? = some key := by
    simpa only [footprint.2.1] using keyFound
  obtain ⟨actual,q,k,qFound,kFound,kWord,slot⟩ := covered entry oldMember kid owner
  have sameKey : k = key := Option.some.inj (kFound.symm.trans oldKey)
  subst k
  have sameTarget : actual = target := Option.some.inj (kWord.symm.trans word)
  subst actual
  have different : target ≠ pid := by
    intro same
    subst target
    rw [vacant] at qFound
    cases qFound
  have oldPeer : before.peers[target]? = some p :=
    (footprint.2.2 target different).symm.trans resident
  simpa only [epoch] using reserved entry oldMember kid key target p
    owner oldKey word oldPeer dead
end Leanux.Proofs.WG.Index
