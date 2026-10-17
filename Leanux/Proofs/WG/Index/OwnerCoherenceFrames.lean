import Leanux.Proofs.WG.Index.OwnerCoherenceModel
import Leanux.Proofs.WG.Index.StoreFieldFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Acquiring an actual resident peer preserves every embedded owner's word
and can only increase the referenced peer's count. -/
theorem ownerCoherent_acquire (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (owner : IndexOwner)
    (coherent : OwnerCoherent d owner) :
    OwnerCoherent (acquirePeer d pid p) owner := by
  obtain ⟨target, q, word, targetResident, positive, identity⟩ := coherent
  have unchangedWord := acquirePeer_word d pid p owner (some target) resident word
  by_cases same : pid = target
  · subst target
    have equal : q = p := Option.some.inj (targetResident.symm.trans resident)
    subst q
    refine ⟨pid, { p with refcount := p.refcount + 1 }, unchangedWord, ?_, by simp, ?_⟩
    · simp [acquirePeer]
    · cases owner <;> exact identity
  · refine ⟨target, q, unchangedWord, ?_, positive, ?_⟩
    · simpa [acquirePeer, Std.TreeMap.getElem?_insert, same] using targetResident
    · cases owner <;> exact identity

/-- A same-value owner-word store retains every peer lookup, including the
writer/queried-peer alias. No TreeMap representation equality is asserted. -/
theorem writeOwnerWord_same_peers (d : Device) (owner : IndexOwner) (word : Option PeerId)
    (same : ownerWord d owner = some word) (pid : PeerId) :
    (writeOwnerWord d owner word).peers[pid]? = d.peers[pid]? := by
  cases owner with
  | handshake own =>
    cases resident : d.peers[own]? with
    | none => simp [ownerWord, resident] at same
    | some p =>
      have value : p.handshakeEntryPeer = word := by simpa [ownerWord, resident] using same
      by_cases alias : own = pid
      · subst pid
        simp [writeOwnerWord, resident, ← value]
      · simp [writeOwnerWord, resident, Std.TreeMap.getElem?_insert, alias]
  | keypair id =>
    cases resident : d.keypairs[id]? <;> simp [writeOwnerWord, resident]

/-- The same owner-word store also retains every keypair lookup. -/
theorem writeOwnerWord_same_keypairs (d : Device) (owner : IndexOwner) (word : Option PeerId)
    (same : ownerWord d owner = some word) (id : KeypairId) :
    (writeOwnerWord d owner word).keypairs[id]? = d.keypairs[id]? := by
  cases owner with
  | handshake pid =>
    cases resident : d.peers[pid]? <;> simp [writeOwnerWord, resident]
  | keypair own =>
    cases resident : d.keypairs[own]? with
    | none => simp [ownerWord, resident] at same
    | some k =>
      have value : k.peer = word := by simpa [ownerWord, resident] using same
      by_cases alias : own = id
      · subst id
        simp [writeOwnerWord, resident, ← value]
      · simp [writeOwnerWord, resident, Std.TreeMap.getElem?_insert, alias]

/-- Storeback of the word just read preserves arbitrary owner coherence. -/
theorem ownerCoherent_write_same (d : Device) (writer owner : IndexOwner)
    (word : Option PeerId) (same : ownerWord d writer = some word)
    (coherent : OwnerCoherent d owner) :
    OwnerCoherent (writeOwnerWord d writer word) owner := by
  obtain ⟨pid, p, value, resident, positive, identity⟩ := coherent
  refine ⟨pid, p, ?_, ?_, positive, ?_⟩
  · cases owner <;> simpa only [ownerWord,
      writeOwnerWord_same_peers d writer word same,
      writeOwnerWord_same_keypairs d writer word same] using value
  · rw [writeOwnerWord_same_peers d writer word same]
    exact resident
  · cases owner with
    | handshake own => exact identity
    | keypair id =>
      obtain ⟨k, stored, live⟩ := identity
      exact ⟨k, (writeOwnerWord_same_keypairs d writer word same id).trans stored, live⟩

end Leanux.Proofs.WG.Index
