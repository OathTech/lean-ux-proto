import PairIndexDecode
import PairIndexStorageProof

namespace Binary.Pair.Index
open Leanux Leanux.WG

/-- The only locations containing hlist links: bucket heads and the two
words in an embedded node. Membership follows from reconstruction. -/
inductive LinkSlot (n : Names) (o : Offsets) : Nat → Prop
  | table (b : Nat) (valid : b<8192) : LinkSlot n o (tableHead n o b)
  | entry (owner : IndexOwner) (base offset : Nat) (named : (owner,base) ∈ n.owners)
      (offsetIs : offset=8 ∨ offset=16) : LinkSlot n o (base+offset)

theorem LinkSlot.bounded {n o address} (slot : LinkSlot n o address)
    (layout : Layout o) (storage : storageCheck n o=true) : address+8≤2^64 := by
  cases slot with
  | table b valid =>
    have bound := (storage_bounds storage (table_storage n o)).2
    simp only [tableHead,layout.buckets,layout.headSize,layout.first,layout.tableSize] at *
    omega
  | entry owner base offset named offsetIs =>
    have bound := entry_bound storage named
    rw [layout.entrySize] at bound
    rcases offsetIs with rfl | rfl <;> omega

theorem LinkSlot.disjoint {n o a b} (left : LinkSlot n o a) (right : LinkSlot n o b)
    (layout : Layout o) (storage : storageCheck n o=true) (different : a≠b) :
    ∀ address, InRange (.ofNat 64 a) 8 address → ¬InRange (.ofNat 64 b) 8 address := by
  cases left with
  | table x xv =>
    cases right with
    | table y yv =>
      apply storage_slices_apart storage (table_storage n o) (table_storage n o)
      · simp only [tableHead,layout.buckets,layout.headSize,layout.first,layout.tableSize]; omega
      · simp only [tableHead,layout.buckets,layout.headSize,layout.first,layout.tableSize]; omega
      · intro _
        simp only [tableHead,layout.buckets,layout.headSize,layout.first] at *
        omega
    | entry owner base offset named offsetIs =>
      apply storage_slices_apart storage (table_storage n o) (entry_storage named)
      · simp only [tableHead,layout.buckets,layout.headSize,layout.first,layout.tableSize]; omega
      · rw [layout.entrySize]
        rcases offsetIs with rfl | rfl <;> omega
      · intro same
        have sizes := congrArg Prod.snd same
        rw [layout.tableSize,layout.entrySize] at sizes
        omega
  | entry owner base offset named offsetIs =>
    cases right with
    | table y yv =>
      apply storage_slices_apart storage (entry_storage named) (table_storage n o)
      · rw [layout.entrySize]
        rcases offsetIs with rfl | rfl <;> omega
      · simp only [tableHead,layout.buckets,layout.headSize,layout.first,layout.tableSize]; omega
      · intro same
        have sizes := congrArg Prod.snd same
        rw [layout.tableSize,layout.entrySize] at sizes
        omega
    | entry other otherBase otherOffset otherNamed otherOffsetIs =>
      apply entry_fields_apart storage named otherNamed
      · rw [layout.entrySize]
        rcases offsetIs with rfl | rfl <;> decide
      · rw [layout.entrySize]
        rcases otherOffsetIs with rfl | rfl <;> decide
      · intro same
        rcases offsetIs with rfl | rfl <;> rcases otherOffsetIs with rfl | rfl <;> omega

theorem NodeFields.nextSlot {n o m b link prev next entry}
    (fields : NodeFields n o m b link prev next entry) (layout : Layout o) :
    LinkSlot n o (link+o.next) := by
  have address : link-o.hash+8=link+o.next := by
    have := fields.valid
    rw [layout.hash,layout.next] at *
    omega
  rw [←address]
  exact .entry _ _ _ fields.named (.inl rfl)

theorem NodeFields.backSlot {n o m b link prev next entry}
    (fields : NodeFields n o m b link prev next entry) (layout : Layout o) :
    LinkSlot n o (link+o.pprev) := by
  have address : link-o.hash+16=link+o.pprev := by
    have := fields.valid
    rw [layout.hash,layout.pprev] at *
    omega
  rw [←address]
  exact .entry _ _ _ fields.named (.inr rfl)

theorem Chain.predecessor_slot {n o m b root nodes link prev next entry}
    (shape : Chain n o m b root nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m b link prev next entry)
    (layout : Layout o) (rootSlot : LinkSlot n o root) : LinkSlot n o prev := by
  rcases shape.back_origin member fields with ⟨atRoot,_⟩ | ⟨parent,current,previous,_,address,parentFields⟩
  · exact atRoot ▸ rootSlot
  · exact address ▸ parentFields.nextSlot layout

inductive DataSlot (n : Names) (o : Offsets) : Nat → Nat → Prop
  | entry (owner : IndexOwner) (base offset size : Nat) (named : (owner,base) ∈ n.owners)
      (field : (offset,size)=(0,8) ∨ (offset,size)=(24,4) ∨ (offset,size)=(28,4)) :
      DataSlot n o (base+offset) size
  | count (id base : Nat) (named : (id,base) ∈ n.peers) :
      DataSlot n o (base+o.peerRefcount) 4

/-- The peer word, type/index scalars and peer counts are outside every
hlist-link store, even when a handshake entry is embedded in its peer. -/
theorem DataSlot.disjoint_link {n o a size b} (left : DataSlot n o a size)
    (right : LinkSlot n o b) (layout : Layout o) (storage : storageCheck n o=true) :
    ∀ address, InRange (.ofNat 64 a) size address → ¬InRange (.ofNat 64 b) 8 address := by
  cases left with
  | entry owner base offset size named field =>
    have fieldBounds : offset+size≤o.entrySize := by
      rw [layout.entrySize]
      rcases field with h | h | h <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj h <;> decide
    cases right with
    | table y yv =>
      apply storage_slices_apart storage (entry_storage named) (table_storage n o)
      · exact ⟨by omega,by omega⟩
      · simp only [tableHead,layout.buckets,layout.headSize,layout.first,layout.tableSize]; omega
      · intro same
        have sizes := congrArg Prod.snd same
        rw [layout.tableSize,layout.entrySize] at sizes
        omega
    | entry other otherBase otherOffset otherNamed offsetIs =>
      apply entry_fields_apart storage named otherNamed fieldBounds
      · rw [layout.entrySize]
        rcases offsetIs with rfl | rfl <;> decide
      · intro _
        rcases field with h | h | h <;> obtain ⟨rfl,rfl⟩ := Prod.mk.inj h <;>
          rcases offsetIs with rfl | rfl <;> decide
  | count id base named =>
    cases right with
    | table y yv =>
      apply storage_slices_apart storage (count_storage named) (table_storage n o)
      · exact ⟨by omega,by omega⟩
      · simp only [tableHead,layout.buckets,layout.headSize,layout.first,layout.tableSize]; omega
      · intro same
        have sizes := congrArg Prod.snd same
        rw [layout.tableSize] at sizes
        omega
    | entry other otherBase otherOffset otherNamed offsetIs =>
      apply storage_slices_apart storage (count_storage named) (entry_storage otherNamed)
      · exact ⟨by omega,by omega⟩
      · rw [layout.entrySize]
        rcases offsetIs with rfl | rfl <;> omega
      · intro same
        have sizes := congrArg Prod.snd same
        rw [layout.entrySize] at sizes
        omega

theorem table_entry_ne {n o owner base offset b}
    (layout : Layout o) (storage : storageCheck n o=true)
    (named : (owner,base) ∈ n.owners) (within : offset<o.entrySize) (bucket : b<8192) :
    tableHead n o b≠base+offset := by
  have separate := storage_apart storage (table_storage n o) (entry_storage named) (by
    intro same
    have sizes := congrArg Prod.snd same
    rw [layout.tableSize,layout.entrySize] at sizes
    omega)
  simp only [tableHead,layout.buckets,layout.headSize,layout.first,layout.tableSize] at *
  rcases separate with first | second <;> omega

theorem NodeFields.root_ne_next {n o m b link prev next entry rootBucket}
    (fields : NodeFields n o m b link prev next entry)
    (layout : Layout o) (storage : storageCheck n o=true) (bucket : rootBucket<8192) :
    tableHead n o rootBucket≠link+o.next := by
  have address : link-o.hash+8=link+o.next := by
    have := fields.valid
    rw [layout.hash,layout.next] at *
    omega
  rw [←address]
  exact table_entry_ne layout storage fields.named (by rw [layout.entrySize]; decide) bucket

theorem address_ne_of_disjoint {a b : Nat}
    (apart : ∀ address, InRange (.ofNat 64 a) 8 address → ¬InRange (.ofNat 64 b) 8 address) : a≠b := by
  intro same
  subst b
  have self : InRange (.ofNat 64 a) 8 (.ofNat 64 a) := ⟨0,by decide,by simp⟩
  exact apart _ self self

theorem NodeFields.next_ne_back {n o m b otherB link prev next entry other otherPrev otherNext otherEntry}
    (fields : NodeFields n o m b link prev next entry)
    (otherFields : NodeFields n o m otherB other otherPrev otherNext otherEntry)
    (layout : Layout o) (storage : storageCheck n o=true) : link+o.next≠other+o.pprev := by
  have nextAddress : link-o.hash+8=link+o.next := by
    have := fields.valid
    rw [layout.hash,layout.next] at *
    omega
  have backAddress : other-o.hash+16=other+o.pprev := by
    have := otherFields.valid
    rw [layout.hash,layout.pprev] at *
    omega
  rw [←nextAddress,←backAddress]
  apply address_ne_of_disjoint
  exact entry_fields_apart storage fields.named otherFields.named
    (by rw [layout.entrySize]; decide) (by rw [layout.entrySize]; decide) (fun _ => by decide)

#print axioms LinkSlot.disjoint
#print axioms Chain.predecessor_slot
#print axioms DataSlot.disjoint_link
end Binary.Pair.Index
