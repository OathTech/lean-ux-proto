import Leanux.WG.Peer

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG

deriving instance ReflBEq, LawfulBEq for IndexOwner

/-- Distinct embedded entries never occupy the same numeric index. -/
def UniqueIndices (table : List IndexEntry) : Prop :=
  table.Pairwise (fun a b => a.index ≠ b.index)

/-- Each embedded entry is hashed at most once. -/
def UniqueOwners (table : List IndexEntry) : Prop :=
  table.Pairwise (fun a b => a.owner ≠ b.owner)

def removeOwner (owner : IndexOwner) (table : List IndexEntry) : List IndexEntry :=
  table.filter (fun e => !(e.owner == owner))

def replaceOwner (pid : PeerId) (kp : KeypairId) (table : List IndexEntry) : List IndexEntry :=
  table.map fun e => if e.owner == .handshake pid then { e with owner := .keypair kp } else e

theorem remove_indices (owner : IndexOwner) (table : List IndexEntry)
    (h : UniqueIndices table) : UniqueIndices (removeOwner owner table) := by
  exact h.filter _

theorem remove_owners (owner : IndexOwner) (table : List IndexEntry)
    (h : UniqueOwners table) : UniqueOwners (removeOwner owner table) := by
  exact h.filter _

theorem remove_absent (owner : IndexOwner) (table : List IndexEntry) :
    ∀ e ∈ removeOwner owner table, e.owner ≠ owner := by
  simp [removeOwner]

theorem replace_indices (pid : PeerId) (kp : KeypairId) (table : List IndexEntry)
    (h : UniqueIndices table) : UniqueIndices (replaceOwner pid kp table) := by
  unfold UniqueIndices replaceOwner
  rw [List.pairwise_map]
  exact h.imp (by intro a b hab; split <;> split <;> exact hab)

theorem replace_owners (pid : PeerId) (kp : KeypairId) (table : List IndexEntry)
    (h : UniqueOwners table) (fresh : ∀ e ∈ table, e.owner ≠ .keypair kp) :
    UniqueOwners (replaceOwner pid kp table) := by
  unfold UniqueOwners replaceOwner
  rw [List.pairwise_map]
  apply h.imp_of_mem
  intro a b ha hb different
  have fa := fresh a ha
  have fb := fresh b hb
  split <;> split <;> simp_all
  all_goals grind

theorem insert_indices (owner : IndexOwner) (index : Nat) (table : List IndexEntry)
    (h : UniqueIndices table)
    (fresh : ∀ e ∈ removeOwner owner table, index ≠ e.index) :
    UniqueIndices ({ index, owner } :: removeOwner owner table) := by
  exact List.pairwise_cons.mpr ⟨fresh, remove_indices owner table h⟩

theorem insert_owners (owner : IndexOwner) (index : Nat) (table : List IndexEntry)
    (h : UniqueOwners table) :
    UniqueOwners ({ index, owner } :: removeOwner owner table) := by
  refine List.pairwise_cons.mpr ⟨?_, remove_owners owner table h⟩
  intro e he
  exact Ne.symm (remove_absent owner table e he)

def bucket (index : Nat) (table : List IndexEntry) : List IndexEntry :=
  table.filter (·.index % (2 ^ INDEX_HASHTABLE_BITS) == index % (2 ^ INDEX_HASHTABLE_BITS))

end Leanux.Proofs.WG.Index
