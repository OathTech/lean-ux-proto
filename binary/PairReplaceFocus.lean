import PairReplaceMemory
import PairUnlinkOwnership
import PairBucketReplace

namespace Binary.Pair.Index
open Leanux Leanux.WG

structure ReplaceFocus (n : Names) (o : Offsets) (m : DataMem) where
  old : UnlinkFocus n o m
  newOwner : IndexOwner
  base : Nat
  named : (newOwner,base) ∈ n.owners
  kind : word m "replace.new.kind" (base+o.kind) 4=.ok (ownerKind newOwner)
  unlinked : word m "owner.pprev" (base+o.hash+o.pprev) 8=.ok 0

namespace ReplaceFocus
def link {n o m} (f : ReplaceFocus n o m) : Nat := f.base+o.hash
def after {n o m} (f : ReplaceFocus n o m) : DataMem :=
  replaceMemory m o f.old.removed f.link f.old.previous f.old.next f.old.entry.index

theorem nonzero {n o m} (f : ReplaceFocus n o m) (layout : Layout o) : f.link≠0 := by
  simp only [link,layout.hash]
  omega

theorem nextSlot {n o m} (f : ReplaceFocus n o m) (layout : Layout o) : LinkSlot n o (f.link+o.next) := by
  simp only [link,layout.hash,layout.next,Nat.add_zero]
  exact .entry f.newOwner f.base 8 f.named (.inl rfl)

theorem backSlot {n o m} (f : ReplaceFocus n o m) (layout : Layout o) : LinkSlot n o (f.link+o.pprev) := by
  simp only [link,layout.hash,layout.pprev,Nat.add_assoc]
  exact .entry f.newOwner f.base 16 f.named (.inr rfl)

theorem different {n o m b old prev next entry} (f : ReplaceFocus n o m)
    (fields : NodeFields n o m b old prev next entry) (previous : prev≠0) : old≠f.link := by
  intro same
  have read := fields.back
  rw [same] at read
  exact previous (word_values read f.unlinked)

theorem absent {n o m b nodes} (f : ReplaceFocus n o m)
    (layout : Layout o) (table : 0<n.table)
    (shape : Chain n o m b (tableHead n o b) nodes) : f.link ∉ nodes.map Prod.fst := by
  intro member
  obtain ⟨⟨address,entry⟩,present,equal⟩ := List.mem_map.mp member
  change address=f.link at equal
  obtain ⟨prev,next,fields⟩ := shape.member_fields present
  apply f.different fields _ equal
  rcases shape.back_origin present fields with ⟨atRoot,_⟩ | ⟨parent,current,previous,_,atParent,parentFields⟩
  · rw [atRoot]
    simp only [tableHead,layout.buckets,layout.headSize,layout.first]
    omega
  · rw [←atParent,layout.next]
    simpa using parentFields.nonzero

theorem old_different {n o m} (f : ReplaceFocus n o m)
    (layout : Layout o) (table : 0<n.table) : f.old.removed≠f.link :=
  f.different f.old.fields (f.old.previous_nonzero layout table)

theorem next_different {n o m} (f : ReplaceFocus n o m) (layout : Layout o) : f.old.next≠f.link := by
  by_cases zero : f.old.next=0
  · rw [zero]; exact Ne.symm (f.nonzero layout)
  · obtain ⟨entry,next,fields⟩ := f.old.nextFields zero
    exact f.different fields (by rw [layout.next]; simpa using f.old.fields.nonzero)

theorem previous_different {n o m} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (table : 0<n.table) :
    f.old.previous≠f.link+o.next := by
  rcases f.old.shape.back_origin f.old.member f.old.fields with ⟨atRoot,_⟩ | ⟨parent,current,previous,member,address,fields⟩
  · rw [atRoot]
    simp only [link,layout.hash,layout.next,Nat.add_zero]
    exact table_entry_ne layout storage f.named (by rw [layout.entrySize]; decide) f.old.validBucket
  · rw [←address]
    have absent := f.absent layout table f.old.shape
    intro equal
    have same : parent=f.link := by omega
    exact absent (List.mem_map.mpr ⟨(parent,current),member,same⟩)

theorem next_ne_back {n o m b old prev next entry} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true)
    (fields : NodeFields n o m b old prev next entry) : f.link+o.next≠old+o.pprev := by
  have back : old-o.hash+16=old+o.pprev := by
    have := fields.valid
    rw [layout.hash,layout.pprev] at *
    omega
  rw [←back]
  simp only [link,layout.hash,layout.next,Nat.add_zero]
  apply address_ne_of_disjoint
  simpa only [layout.hash] using entry_fields_apart (offset := 8) (size := 8) (otherOffset := 16) (otherSize := 8) storage f.named fields.named
    (by rw [layout.entrySize]; decide) (by rw [layout.entrySize]; decide) (fun _ => by decide)

theorem next_ne_newback {n o m b old prev next entry} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true)
    (fields : NodeFields n o m b old prev next entry) : old+o.next≠f.link+o.pprev := by
  have next : old-o.hash+8=old+o.next := by
    have := fields.valid
    rw [layout.hash,layout.next] at *
    omega
  rw [←next]
  simp only [link,layout.hash,layout.pprev,Nat.add_assoc]
  apply address_ne_of_disjoint
  simpa only [layout.hash] using entry_fields_apart (offset := 8) (size := 8) (otherOffset := 16) (otherSize := 8) storage fields.named f.named
    (by rw [layout.entrySize]; decide) (by rw [layout.entrySize]; decide) (fun _ => by decide)

theorem read_link {n o m} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (path : String)
    {address : Nat} (slot : LinkSlot n o address) :
    word f.after path address 8=wordEffect address (word m path address 8)
      (replacementStores o f.old.removed f.link f.old.previous f.old.next) :=
  replacement_word f.old layout storage f.named rfl path slot _

#print axioms absent
#print axioms previous_different
end ReplaceFocus
end Binary.Pair.Index
