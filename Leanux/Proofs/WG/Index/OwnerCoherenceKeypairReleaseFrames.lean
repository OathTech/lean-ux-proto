import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.ReleaseEffects

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- The actual release transform unhashes a removed key before erasing it;
a retained hashed key keeps its peer word and a positive reference. -/
theorem releasedDevice_owner_coherent (d : Device) (id : KeypairId) (k : Keypair)
    (now : Bool) (resident : d.keypairs[id]? = some k) (live : 0 < k.refcount)
    (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (releasedDevice d id k now) := by
  have peers : (releasedDevice d id k now).peers = d.peers := by
    cases now <;> by_cases last : k.refcount = 1 <;>
      simp [releasedDevice, unhashKeypair, last]
  intro e member
  have oldMember : e ∈ d.indexTable := by
    rw [released_table] at member
    split at member
    · exact (List.mem_filter.mp member).1
    · exact member
  have old := coherent e oldMember
  cases owner : e.owner with
  | handshake pid => simpa only [OwnerCoherent, owner, ownerWord, peers] using old
  | keypair other =>
    by_cases same : id = other
    · subst other
      have notLast : k.refcount ≠ 1 := by
        intro last
        exact released_unhashed d id k now (.inr last) e member owner
      obtain ⟨pid, p, word, found, positive, key⟩ := old
      have value : k.peer = some pid := by simpa [ownerWord, owner, resident] using word
      refine ⟨pid, p, ?_, ?_, positive, ?_⟩
      · simp [ownerWord, released_keypair, notLast, value]
      · rw [peers]
        exact found
      · refine ⟨{k with refcount := k.refcount - 1}, ?_, ?_⟩
        · simp [released_keypair, notLast]
        · change 0 < k.refcount - 1
          omega
    · simpa only [OwnerCoherent, owner, ownerWord,
        released_other_keypair d id other k now same, peers] using old

end Leanux.Proofs.WG.Index
