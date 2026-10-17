import Leanux.Proofs.WG.Index.OwnerCoherenceModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

/-- Removing table rows does not change any owner object or referenced peer. -/
theorem hashedOwnersCoherent_remove (d : Device) (owner : IndexOwner)
    (coherent : HashedOwnersCoherent d) :
    HashedOwnersCoherent {d with indexTable := removeOwner owner d.indexTable} := by
  intro e member
  exact coherent e (List.mem_filter.mp member).1

/-- Insertion adds one explicitly coherent owner after unhashing its old row.
No numeric-index or owner uniqueness premise is needed for this relation. -/
theorem hashedOwnersCoherent_insert (d : Device) (owner : IndexOwner) (index : Nat)
    (coherent : HashedOwnersCoherent d) (published : OwnerCoherent d owner) :
    HashedOwnersCoherent
      {d with indexTable := {index, owner} :: removeOwner owner d.indexTable} := by
  intro e member
  rcases List.mem_cons.mp member with same | old
  · subst e
    exact published
  · exact coherent e (List.mem_filter.mp old).1

/-- Handshake replacement publishes the destination keypair's own peer word.
Its coherence is an explicit local obligation, even when already hashed. -/
theorem hashedOwnersCoherent_replace (d : Device) (pid : PeerId) (kp : KeypairId)
    (coherent : HashedOwnersCoherent d) (published : OwnerCoherent d (.keypair kp)) :
    HashedOwnersCoherent {d with indexTable := replaceOwner pid kp d.indexTable} := by
  intro e member
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
  split
  · exact published
  · exact coherent old oldMember

end Leanux.Proofs.WG.Index
