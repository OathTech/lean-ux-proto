import PairUnlinkMemory
import PairIndexSlots

namespace Binary.Pair.Index
open Leanux Leanux.WG

/-- A focus extracted from one successful bucket traversal. These are
derived facts about the current heap, not future execution assumptions. -/
structure UnlinkFocus (n : Names) (o : Offsets) (m : DataMem) where
  bucket : Nat
  validBucket : bucket<8192
  nodes : Nodes
  removed : Nat
  previous : Nat
  next : Nat
  entry : IndexEntry
  shape : Chain n o m bucket (tableHead n o bucket) nodes
  member : (removed,entry) ∈ nodes
  fields : NodeFields n o m bucket removed previous next entry
  headRead : word m "bucket.head" (tableHead n o bucket) 8=.ok (head nodes)

namespace UnlinkFocus

theorem previousSlot {n o m} (f : UnlinkFocus n o m) (layout : Layout o) :
    LinkSlot n o f.previous :=
  f.shape.predecessor_slot f.member f.fields layout (.table _ f.validBucket)

theorem nextFields {n o m} (f : UnlinkFocus n o m) (nonzero : f.next≠0) :
    ∃ entry next, NodeFields n o m f.bucket f.next (f.removed+o.next) next entry :=
  f.shape.successor f.member f.fields nonzero

theorem storeSlots {n o m} (f : UnlinkFocus n o m) (layout : Layout o)
    {destination : Nat}
    (member : destination ∈ f.previous::(f.removed+o.pprev)::(if f.next=0 then [] else [f.next+o.pprev])) :
    LinkSlot n o destination := by
  rcases List.mem_cons.mp member with rfl | member
  · exact f.previousSlot layout
  rcases List.mem_cons.mp member with rfl | member
  · exact f.fields.backSlot layout
  by_cases zero : f.next=0
  · simp only [zero,↓reduceIte,List.not_mem_nil] at member
  · have address : destination=f.next+o.pprev := by simpa only [zero,↓reduceIte,List.mem_singleton] using member
    rw [address]
    obtain ⟨entry,next,fields⟩ := f.nextFields zero
    exact fields.backSlot layout

theorem read_link {n o m} (f : UnlinkFocus n o m) (layout : Layout o)
    (storage : storageCheck n o=true) (path : String) {address : Nat} (slot : LinkSlot n o address) :
    word (unlinkMemory m o f.removed f.previous f.next) path address 8 =
      if address=f.removed+o.pprev then .ok 0 else
      if f.next≠0 ∧ address=f.next+o.pprev then .ok f.previous else
      if address=f.previous then .ok f.next else word m path address 8 := by
  apply unlink_word _ _ _ _ _ _ _ (slot.bounded layout storage)
    (by have := word_bound f.fields.back; simpa using this)
    (by have := word_bound f.fields.forward; simpa using this)
  intro destination member different
  exact slot.disjoint (f.storeSlots layout member) layout storage different

theorem read_data {n o m} (f : UnlinkFocus n o m) (layout : Layout o)
    (storage : storageCheck n o=true) (path : String) {address size : Nat} (slot : DataSlot n o address size) :
    word (unlinkMemory m o f.removed f.previous f.next) path address size=word m path address size := by
  apply unlink_word_frame
  intro address inside writes
  rcases writes with previous | ⟨nonzero,next⟩ | removed
  · exact slot.disjoint_link (f.previousSlot layout) layout storage address inside previous
  · obtain ⟨entry,tail,fields⟩ := f.nextFields nonzero
    exact slot.disjoint_link (fields.backSlot layout) layout storage address inside next
  · exact slot.disjoint_link (f.fields.backSlot layout) layout storage address inside removed

theorem back_ne_previous {n o m b link previous next entry} (f : UnlinkFocus n o m)
    (fields : NodeFields n o m b link previous next entry)
    (layout : Layout o) (storage : storageCheck n o=true) : link+o.pprev≠f.previous := by
  rcases f.shape.back_origin f.member f.fields with ⟨atRoot,_⟩ | ⟨parent,current,prev,_,address,parentFields⟩
  · rw [atRoot]
    have base : link-o.hash+16=link+o.pprev := by
      have := fields.valid
      rw [layout.hash,layout.pprev] at *
      omega
    rw [←base]
    exact Ne.symm (table_entry_ne layout storage fields.named (by rw [layout.entrySize]; decide) f.validBucket)
  · rw [←address]
    exact Ne.symm (parentFields.next_ne_back fields layout storage)

theorem remaining_fields {n o m b nodes link previous next entry} (f : UnlinkFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (bucket : b<8192)
    (shape : Chain n o m b (tableHead n o b) nodes) (member : (link,entry) ∈ nodes)
    (fields : NodeFields n o m b link previous next entry) (different : link≠f.removed) :
    NodeFields n o (unlinkMemory m o f.removed f.previous f.next) b link
      (skip (f.removed+o.next) f.previous previous) (skip f.removed f.next next) entry := by
  have neighbor := shape.neighbor_addresses member fields f.shape f.member f.fields
    (f.fields.root_ne_next layout storage bucket)
    (f.shape.predecessor_read f.member f.fields f.headRead)
  refine ⟨fields.nonzero,fields.valid,fields.owner,?_,fields.bucket,?_,?_,?_⟩
  · rw [f.read_data layout storage _ (by
      rw [layout.index]
      exact .entry _ _ 28 4 fields.named (.inr (.inr rfl)))]
    exact fields.index
  · rw [f.read_data layout storage _ (by
      rw [layout.kind]
      exact .entry _ _ 24 4 fields.named (.inr (.inl rfl)))]
    exact fields.kind
  · rw [f.read_link layout storage _ (fields.backSlot layout)]
    have clearNe : link+o.pprev≠f.removed+o.pprev := by omega
    have nextEq : (f.next≠0 ∧ link+o.pprev=f.next+o.pprev) ↔ previous=f.removed+o.next := by
      rw [neighbor.2]
      constructor
      · rintro ⟨_,equal⟩; omega
      · intro equal; exact ⟨equal ▸ fields.nonzero,by omega⟩
    simp only [clearNe,↓reduceIte,f.back_ne_previous fields layout storage,nextEq,fields.back,skip]
    split <;> rfl
  · rw [f.read_link layout storage _ (fields.nextSlot layout)]
    have clearNe := fields.next_ne_back f.fields layout storage
    have nextNe : ¬(f.next≠0 ∧ link+o.next=f.next+o.pprev) := by
      rintro ⟨nonzero,equal⟩
      obtain ⟨entry,tail,successor⟩ := f.nextFields nonzero
      exact fields.next_ne_back successor layout storage equal
    simp only [clearNe,↓reduceIte,nextNe,←neighbor.1,fields.forward,skip]
    split <;> rfl

#print axioms remaining_fields
end UnlinkFocus
end Binary.Pair.Index
