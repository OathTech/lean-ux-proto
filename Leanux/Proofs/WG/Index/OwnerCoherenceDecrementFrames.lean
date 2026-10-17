import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.ReleaseModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Decrementing an actual resident peer with another reference retains owner
coherence, including aliases between the released peer and a hashed owner. -/
theorem nonlastPeerRelease_coherent (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (retained : 1 < p.refcount)
    (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent (releasedPeerDevice d pid p) := by
  have notLast : p.refcount ≠ 1 := by omega
  have word_same (owner : IndexOwner) :
      ownerWord (releasedPeerDevice d pid p) owner = ownerWord d owner := by
    cases owner with
    | keypair id => simp [ownerWord, releasedPeerDevice, notLast]
    | handshake own =>
      by_cases same : pid = own
      · subst own
        simp [ownerWord, releasedPeerDevice, notLast, resident]
      · simp [ownerWord, releasedPeerDevice, notLast, Std.TreeMap.getElem?_insert, same]
  intro e member
  have oldMember : e ∈ d.indexTable := by
    simpa only [releasedPeerDevice, ite_eq_right notLast] using member
  obtain ⟨target, q, word, found, positive, owned⟩ := coherent e oldMember
  by_cases same : pid = target
  · subst target
    have equal : q = p := Option.some.inj (found.symm.trans resident)
    subst q
    refine ⟨pid, {p with refcount := p.refcount - 1}, ?_, ?_, ?_, ?_⟩
    · rw [word_same]
      exact word
    · simp [releasedPeerDevice, notLast]
    · change 0 < p.refcount - 1
      omega
    · cases ownerEq : e.owner with
      | handshake own => simpa only [ownerEq] using owned
      | keypair id => simpa [ownerEq, releasedPeerDevice, notLast] using owned
  · refine ⟨target, q, ?_, ?_, positive, ?_⟩
    · rw [word_same]
      exact word
    · simpa [releasedPeerDevice, notLast, Std.TreeMap.getElem?_insert, same] using found
    · cases ownerEq : e.owner with
      | handshake own => simpa only [ownerEq] using owned
      | keypair id => simpa [ownerEq, releasedPeerDevice, notLast] using owned

end Leanux.Proofs.WG.Index
