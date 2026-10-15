import Representation
import OwnerWord

namespace Binary.IndexHeap
open Leanux.WG

/-- The link is the address of the pointer to this node: a bucket head or
    the preceding node's next word. pprev points to that word, not its value.
    Owner words and allocation lifetimes are separate components. -/
def Chain (memory : Mem 64) (entry : IndexOwner → Address) :
    Address → List IndexEntry → Prop
  | link, [] => memory.loadInt link 8 = some 0
  | link, e :: rest =>
      link ≠ 0 ∧ entry e.owner ≠ 0 ∧ entry e.owner + .ofNat 64 Layouts.entry_index_hash ≠ 0 ∧
      e.index < 2^32 ∧
      memory.loadInt link 8 = some ((entry e.owner + .ofNat 64 Layouts.entry_index_hash).toNat : Int) ∧
      memory.loadInt (entry e.owner + .ofNat 64 (Layouts.entry_index_hash + Layouts.node_pprev)) 8 =
        some (link.toNat : Int) ∧
      memory.loadInt (entry e.owner + .ofNat 64 Layouts.entry_type) 4 = some (kindWord e.kind).toNat ∧
      memory.loadInt (entry e.owner + .ofNat 64 Layouts.entry_index) 4 = some e.index ∧
      Chain memory entry (entry e.owner + .ofNat 64 Layouts.entry_index_hash) rest

def cells (entry : IndexOwner → Address) (es : List IndexEntry) : List (Address × IndexEntry) :=
  es.map fun e => (entry e.owner, e)

/-- The complete hlist relation supplies the physical loop invariant already
    used by the instruction proofs, without any constraint on peer words. -/
theorem Chain.bucket {memory entry link es} (represented : Chain memory entry link es) :
    ∃ head : Address, memory.loadInt link 8 = some (head.toNat : Int) ∧
      BucketShape memory head (cells entry es) := by
  induction es generalizing link with
  | nil => exact ⟨0, represented, rfl⟩
  | cons e es ih =>
    obtain ⟨linkNonzero, base, node, bound, linked, back, kind, index, tail⟩ := represented
    obtain ⟨next, loaded, shape⟩ := ih tail
    refine ⟨entry e.owner + .ofNat 64 Layouts.entry_index_hash, linked,
      base, node, rfl, bound, kind, index, next, ?_, shape⟩
    simpa only [Layouts.node_next, BitVec.add_zero] using loaded

def Reads (entry : IndexOwner → Address) (link : Address) (es : List IndexEntry)
    (address : Address) : Prop :=
  InRange link 8 address ∨ ∃ e ∈ es,
    BucketShapeReads (entry e.owner) address ∨
      InRange (entry e.owner + .ofNat 64 (Layouts.entry_index_hash + Layouts.node_pprev)) 8 address

theorem Chain.frame {before after entry link es writes}
    (same : EqualOutside writes before after)
    (apart : ∀ address, Reads entry link es address → ¬writes address)
    (represented : Chain before entry link es) : Chain after entry link es := by
  induction es generalizing link with
  | nil => exact (same.loadInt link 8 (fun i hi => apart _ (.inl ⟨i, hi, rfl⟩))).symm.trans represented
  | cons e es ih =>
    obtain ⟨linkNonzero, base, node, bound, linked, back, kind, index, tail⟩ := represented
    have localApart (address) (h : BucketShapeReads (entry e.owner) address ∨
        InRange (entry e.owner + .ofNat 64 (Layouts.entry_index_hash + Layouts.node_pprev)) 8 address) :
        ¬writes address := apart address (.inr ⟨e, by simp, h⟩)
    refine ⟨linkNonzero, base, node, bound, ?_, ?_, ?_, ?_, ?_⟩
    · exact (same.loadInt link 8 (fun i hi => apart _ (.inl ⟨i, hi, rfl⟩))).symm.trans linked
    · exact (same.loadInt _ 8 (fun i hi => localApart _ (.inr ⟨i, hi, rfl⟩))).symm.trans back
    · exact (same.loadInt _ 4 (fun i hi => localApart _ (.inl (.inr (.inl ⟨i, hi, rfl⟩))))).symm.trans kind
    · exact (same.loadInt _ 4 (fun i hi => localApart _ (.inl (.inr (.inr ⟨i, hi, rfl⟩))))).symm.trans index
    · apply ih _ tail
      intro address read
      rcases read with head | ⟨other, member, read⟩
      · exact localApart address (.inl (.inl head))
      · exact apart address (.inr ⟨other, by simp [member], read⟩)

def bucket (es : List IndexEntry) (number : Nat) : List IndexEntry :=
  es.filter (fun e => e.index % 8192 == number)

/-- All buckets, including their backward links. A single physical table
    does not determine the interleaving of entries in different buckets. -/
def Table (memory : Mem 64) (entry : IndexOwner → Address) (device : Address)
    (es : List IndexEntry) : Prop :=
  ∃ table : Address, table ≠ 0 ∧
    memory.loadInt (device + .ofNat 64 Layouts.device_index_hashtable) 8 = some (table.toNat : Int) ∧
    ∀ b < 8192, Chain memory entry
      (table + .ofNat 64 (Layouts.indexTable_hashtable + b * Layouts.headSize)) (bucket es b)

/-- Every member of the bucket is placed at its owning embedded entry. -/
theorem Table.lookup_bucket {memory entry device es} (represented : Table memory entry device es)
    (index : Nat) :
    ∃ table head : Address, table ≠ 0 ∧
      memory.loadInt (device + .ofNat 64 Layouts.device_index_hashtable) 8 = some (table.toNat : Int) ∧
      memory.loadInt (table + .ofNat 64 (Layouts.indexTable_hashtable + index % 8192 * Layouts.headSize)) 8 =
        some (head.toNat : Int) ∧ BucketShape memory head (cells entry (bucket es (index % 8192))) := by
  obtain ⟨table, nonnull, loaded, chains⟩ := represented
  obtain ⟨head, pointer, shape⟩ := (chains (index % 8192) (Nat.mod_lt _ (by decide))).bucket
  exact ⟨table, head, nonnull, loaded, pointer, shape⟩

def TableReads (entry : IndexOwner → Address) (device table : Address)
    (es : List IndexEntry) (address : Address) : Prop :=
  InRange (device + .ofNat 64 Layouts.device_index_hashtable) 8 address ∨
    ∃ b < 8192, Reads entry
      (table + .ofNat 64 (Layouts.indexTable_hashtable + b * Layouts.headSize)) (bucket es b) address

theorem Table.frame {before after entry device es writes}
    (same : EqualOutside writes before after)
    (apart : ∀ table : Address,
      before.loadInt (device + .ofNat 64 Layouts.device_index_hashtable) 8 = some (table.toNat : Int) →
      ∀ address, TableReads entry device table es address → ¬writes address)
    (represented : Table before entry device es) : Table after entry device es := by
  obtain ⟨table, nonnull, loaded, chains⟩ := represented
  refine ⟨table, nonnull, ?_, ?_⟩
  · exact (same.loadInt _ 8 (fun i hi => apart table loaded _ (.inl ⟨i, hi, rfl⟩))).symm.trans loaded
  · intro b bound
    exact (chains b bound).frame same (fun a h => apart table loaded a (.inr ⟨b, bound, h⟩))

/-- The owner store may clear its peer word without changing any of the
    node's forward/backward links, kind or index. Other allocation separation
    is an independent obligation; embedding is allowed. -/
theorem Reads.apart_own_peer (base address : Address)
    (read : BucketShapeReads base address ∨
      InRange (base + .ofNat 64 (Layouts.entry_index_hash + Layouts.node_pprev)) 8 address) :
    ¬InRange base 8 address := by
  rcases read with fields | back
  · exact fields.apart_peer
  · simpa only [BitVec.add_zero] using
      InRange.offset_disjoint base 16 8 0 8 (by decide) (by decide) (by decide) address back

/-- Unhashed pprev is NULL. hlist_del_init_rcu deliberately retains next,
    so no equation is imposed on that stale forward pointer. -/
def Unhashed (memory : Mem 64) (base : Address) : Prop :=
  memory.loadInt (base + .ofNat 64 (Layouts.entry_index_hash + Layouts.node_pprev)) 8 = some 0

/-- Committed index mutations, not lookup decisions or peer-word stores.
    Insertion's preceding unhash is a separate event. These events must be
    justified by actual prior executions when the trace relation is composed. -/
inductive Mutation where
  | unlink (owner : IndexOwner)
  | insert (owner : IndexOwner) (index : Nat)
  | replace (oldOwner newOwner : IndexOwner)

def Mutation.apply (event : Mutation) (es : List IndexEntry) : List IndexEntry :=
  match event with
  | .unlink owner => es.filter (fun e => !(e.owner == owner))
  | .insert owner index => {index, owner} :: es
  | .replace oldOwner newOwner => es.map (fun e => if e.owner == oldOwner then {e with owner := newOwner} else e)

/-- Fixed incoming order plus committed mutation history determines the
    cross-bucket ordering. Neither argument may be chosen anew at a cut. -/
def ordered (incoming : List IndexEntry) (events : List Mutation) : List IndexEntry :=
  events.foldl (fun es event => event.apply es) incoming

theorem ordered_append (incoming : List IndexEntry) (events : List Mutation) (event : Mutation) :
    ordered incoming (events ++ [event]) = event.apply (ordered incoming events) := by
  simp [ordered, List.foldl_append]

#print axioms Chain.bucket
#print axioms Chain.frame
#print axioms Table.lookup_bucket
#print axioms Table.frame
#print axioms Reads.apart_own_peer
#print axioms ordered_append
end Binary.IndexHeap
