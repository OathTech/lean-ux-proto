import Leanux.Proofs.WG.Index.OwnerCoherenceSlotRemovalModel

/-! Hashed keypair rows remain connected to an actual owning peer slot.
This relation is separate from numeric/owner uniqueness and positive reference
counts. It rules out the existing arbitrary-state orphan-row examples. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Noise

def HashSlotCoverage (d : Device) : Prop :=
  ∀ entry ∈ d.indexTable, ∀ kid, entry.owner = .keypair kid →
    ∃ pid p key, d.peers[pid]? = some p ∧ d.keypairs[kid]? = some key ∧
      key.peer = some pid ∧ some kid ∈ clearKeys p

namespace View
def HashSlotsSafe (s : Campaign2.Snapshot) : Prop :=
  ∀ d, s.wg.device = some d → HashSlotCoverage d
end View

theorem hashSlotCoverage_empty (d : Device) (empty : d.indexTable = []) :
    HashSlotCoverage d := by
  intro entry member
  simp only [empty, List.not_mem_nil] at member

theorem hashSlotCoverage_lastOwnerCovered (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) (coherent : HashedOwnersCoherent d)
    (covered : HashSlotCoverage d) : LastOwnerCovered d pid p := by
  intro _ entry member word
  cases owner : entry.owner with
  | handshake target =>
    obtain ⟨actual,peer,actualWord,stored,positive,identity⟩ := coherent entry member
    have same : actual = pid := by
      rw [word] at actualWord
      exact Option.some.inj (Option.some.inj actualWord).symm
    subst actual
    have identity' : pid = target := by simpa only [owner] using identity
    exact Or.inl (congrArg IndexOwner.handshake identity'.symm)
  | keypair kid =>
    obtain ⟨actual,peer,key,stored,keyStored,keyPeer,slot⟩ := covered entry member kid owner
    have same : actual = pid := by
      simpa only [owner,ownerWord,keyStored,Option.map_some,keyPeer,Option.some.injEq] using word
    subst actual
    have samePeer : peer = p := Option.some.inj (stored.symm.trans resident)
    subst peer
    exact Or.inr ⟨kid,rfl,slot⟩

theorem hashSlotCoverage_table_subset (d : Device) (table : List IndexEntry)
    (covered : HashSlotCoverage d) (subset : ∀ entry ∈ table, entry ∈ d.indexTable) :
    HashSlotCoverage {d with indexTable := table} :=
  fun entry member kid owner => covered entry (subset entry member) kid owner

theorem hashSlotCoverage_remove (d : Device) (owner : IndexOwner)
    (covered : HashSlotCoverage d) :
    HashSlotCoverage {d with indexTable := removeOwner owner d.indexTable} := by
  apply hashSlotCoverage_table_subset d _ covered
  intro entry member
  exact (List.mem_filter.mp member).1

end Leanux.Proofs.WG.Index
