import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.PeerRelease

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Under entry coherence, the exact missing obligation on last release is
that no hashed owner surviving the handshake unhash names the released peer. -/
theorem lastPeerRelease_coherent_iff (d : Device) (pid : PeerId) (p : Peer)
    (last : p.refcount = 1) (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (releasedPeerDevice d pid p) ↔
      ∀ e ∈ d.indexTable, e.owner ≠ .handshake pid →
        ownerWord d e.owner ≠ some (some pid) := by
  let final := releasedPeerDevice d pid p
  have word_same (owner : IndexOwner) (kept : owner ≠ .handshake pid) :
      ownerWord final owner = ownerWord d owner := by
    cases owner with
    | keypair id => simp [final, ownerWord, releasedPeerDevice, last]
    | handshake id =>
      have other : id ≠ pid := by intro same; subst id; exact kept rfl
      simp [final, ownerWord, releasedPeerDevice, last, Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_erase, Ne.symm other]
  have member_iff (e : IndexEntry) :
      e ∈ final.indexTable ↔ e ∈ d.indexTable ∧ e.owner ≠ .handshake pid := by
    simp [final, releasedPeerDevice, last, removeOwner]
  have peer_same (id : PeerId) (other : id ≠ pid) :
      final.peers[id]? = d.peers[id]? := by
    simp [final, releasedPeerDevice, last, Std.TreeMap.getElem?_insert, Std.TreeMap.getElem?_erase, Ne.symm other]
  have absent : final.peers[pid]? = none := by simp [final, releasedPeerDevice, last]
  constructor
  · intro safe e member kept word
    obtain ⟨target, peer, targetWord, found, positive, owned⟩ :=
      safe e ((member_iff e).mpr ⟨member, kept⟩)
    rw [word_same e.owner kept, word] at targetWord
    have same : target = pid := by simpa using targetWord.symm
    subst target
    rw [absent] at found
    cases found
  · intro detached e member
    obtain ⟨oldMember, kept⟩ := (member_iff e).mp member
    obtain ⟨target, peer, word, found, positive, owned⟩ := coherent e oldMember
    have other : target ≠ pid := by
      intro same
      subst target
      exact detached e oldMember kept word
    refine ⟨target, peer, ?_, ?_, positive, ?_⟩
    · rw [word_same e.owner kept]
      exact word
    · rw [peer_same target other]
      exact found
    · cases ownerEq : e.owner with
      | handshake own => simpa only [ownerEq] using owned
      | keypair id =>
        simpa [ownerEq, final, releasedPeerDevice, last] using owned

end Leanux.Proofs.WG.Index
