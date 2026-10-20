import PairUnlinkFields
import PairWordPlan
import PairIndexScalar

namespace Binary.Pair.Index

def replacementStores (o : Offsets) (old new previous next : Nat) : List (Nat×Nat) :=
  [(new+o.next,next),(new+o.pprev,previous),(previous,new)] ++
    (if next=0 then [] else [(next+o.pprev,new+o.next)]) ++
    [(old+o.next,0),(old+o.pprev,0xdead000000000122),(old+o.pprev,0)]

def replaceMemory (m : DataMem) (o : Offsets) (old new previous next index : Nat) : DataMem :=
  write64s (write32 m (new-o.hash+o.index) index) (replacementStores o old new previous next)

def replacePrefixMemory (m : DataMem) (o : Offsets) (new previous next index : Nat) : DataMem :=
  write64 (write64 (write64 (write32 m (new-o.hash+o.index) index)
    (new+o.next) next) (new+o.pprev) previous) previous new

theorem replaceMemory_split (m : DataMem) (o : Offsets) (old new previous next index : Nat) :
    replaceMemory m o old new previous next index =
      let first := replacePrefixMemory m o new previous next index
      let repaired := if next=0 then first else write64 first (next+o.pprev) (new+o.next)
      write64 (write64 (write64 repaired (old+o.next) 0) (old+o.pprev) 0xdead000000000122) (old+o.pprev) 0 := by
  by_cases zero : next=0 <;>
    simp [replaceMemory,replacementStores,replacePrefixMemory,write64s,zero]

theorem word_after_index {n o address owner base} (m : DataMem) (value : Nat)
    (layout : Layout o) (storage : storageCheck n o=true) (named : (owner,base) ∈ n.owners)
    (slot : LinkSlot n o address) (path : String) :
    word (write32 m (base+28) value) path address 8=word m path address 8 := by
  have scalar : DataSlot n o (base+28) 4 := .entry owner base 28 4 named (.inr (.inr rfl))
  exact word_write32_frame _ _ _ _ _ _ (by
    intro a link index
    exact scalar.disjoint_link slot layout storage a index link)

theorem replacement_effect (o : Offsets) (old new previous next address : Nat) (before : Decode Nat) :
    wordEffect address before (replacementStores o old new previous next)=
      if address=old+o.pprev then .ok 0 else
      if address=old+o.next then .ok 0 else
      if next≠0 ∧ address=next+o.pprev then .ok (new+o.next) else
      if address=previous then .ok new else
      if address=new+o.pprev then .ok previous else
      if address=new+o.next then .ok next else before := by
  by_cases zero : next=0 <;> by_cases clear : address=old+o.pprev <;>
    simp [replacementStores,wordEffect,zero,clear]

theorem replacement_slots {n o m} (f : UnlinkFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true)
    {owner base : Nat} {newOwner : Leanux.WG.IndexOwner}
    (named : (newOwner,base) ∈ n.owners) (newEq : owner=base+o.hash) :
    ∀ destination value, (destination,value) ∈ replacementStores o f.removed owner f.previous f.next →
      LinkSlot n o destination ∧ value<2^64 := by
  have bound := entry_bound storage named
  have oldNext := f.fields.nextSlot layout
  have oldBack := f.fields.backSlot layout
  have newNext : LinkSlot n o (owner+o.next) := by
    rw [newEq,layout.hash,layout.next,Nat.add_zero]
    exact .entry newOwner base 8 named (.inl rfl)
  have newBack : LinkSlot n o (owner+o.pprev) := by
    rw [newEq,layout.hash,layout.pprev,Nat.add_assoc]
    exact .entry newOwner base 16 named (.inr rfl)
  have newSmall : owner+o.next<2^64 := by
    rw [layout.entrySize] at bound
    rw [newEq,layout.hash,layout.next]
    omega
  intro destination value member
  unfold replacementStores at member
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with ((equal | equal | equal) | member) | equal | equal | equal
  · cases equal; exact ⟨newNext,word_bound f.fields.forward⟩
  · cases equal; exact ⟨newBack,word_bound f.fields.back⟩
  · cases equal; exact ⟨f.previousSlot layout,by omega⟩
  · by_cases zero : f.next=0
    · simp [zero] at member
    · have equal : (destination,value)=(f.next+o.pprev,owner+o.next) := by simpa [zero] using member
      cases equal
      obtain ⟨entry,next,fields⟩ := f.nextFields zero
      exact ⟨fields.backSlot layout,newSmall⟩
  · cases equal; exact ⟨oldNext,by decide⟩
  · cases equal; exact ⟨oldBack,by decide⟩
  · cases equal; exact ⟨oldBack,by decide⟩

theorem replacement_word {n o m} (f : UnlinkFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true)
    {owner base : Nat} {newOwner : Leanux.WG.IndexOwner}
    (named : (newOwner,base) ∈ n.owners) (newEq : owner=base+o.hash)
    (path : String) {address : Nat} (slot : LinkSlot n o address) (index : Nat) :
    word (replaceMemory m o f.removed owner f.previous f.next index) path address 8=
      wordEffect address (word m path address 8) (replacementStores o f.removed owner f.previous f.next) := by
  have planSlots := replacement_slots f layout storage named newEq
  have indexAddress : owner-o.hash+o.index=base+28 := by rw [newEq,layout.hash,layout.index]; omega
  have indexSlot : DataSlot n o (base+28) 4 := .entry newOwner base 28 4 named (.inr (.inr rfl))
  unfold replaceMemory
  rw [word_write64s _ _ _ _ (slot.bounded layout storage)
    (fun a v member => (planSlots a v member).2)
    (fun a v member different => slot.disjoint (planSlots a v member).1 layout storage different)]
  rw [indexAddress,word_write32_frame _ _ _ _ _ _ (by
    intro a link scalar
    exact indexSlot.disjoint_link slot layout storage a scalar link)]

#print axioms replacement_word

theorem replacement_data_frame {n o m} (f : UnlinkFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true)
    {owner base : Nat} {newOwner : Leanux.WG.IndexOwner}
    (named : (newOwner,base) ∈ n.owners) (newEq : owner=base+o.hash)
    (path : String) {address size : Nat} (slot : DataSlot n o address size)
    (different : address≠base+28) (index : Nat) :
    word (replaceMemory m o f.removed owner f.previous f.next index) path address size=
      word m path address size := by
  have plan := replacement_slots f layout storage named newEq
  have indexAddress : owner-o.hash+o.index=base+28 := by rw [newEq,layout.hash,layout.index]; omega
  unfold replaceMemory
  rw [word_write64s_frame _ _ _ _ _ (fun a v member => slot.disjoint_link (plan a v member).1 layout storage)]
  rw [indexAddress]
  exact word_write32_frame _ _ _ _ _ _ (slot.disjoint_index layout storage named different)

theorem replacement_index {n o m} (f : UnlinkFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true)
    {owner base : Nat} {newOwner : Leanux.WG.IndexOwner}
    (named : (newOwner,base) ∈ n.owners) (newEq : owner=base+o.hash)
    (path : String) :
    word (replaceMemory m o f.removed owner f.previous f.next f.entry.index) path (base+28) 4=
      .ok f.entry.index := by
  have plan := replacement_slots f layout storage named newEq
  have indexAddress : owner-o.hash+o.index=base+28 := by rw [newEq,layout.hash,layout.index]; omega
  have slot : DataSlot n o (base+28) 4 := .entry newOwner base 28 4 named (.inr (.inr rfl))
  have bounded := entry_bound storage named
  rw [layout.entrySize] at bounded
  have small := word_bound f.fields.index
  unfold replaceMemory
  rw [word_write64s_frame _ _ _ _ _ (fun a v member => slot.disjoint_link (plan a v member).1 layout storage),indexAddress]
  exact word_write32_same _ _ _ _ (by omega) (by simpa using small)

#print axioms replacement_data_frame
#print axioms replacement_index
end Binary.Pair.Index
