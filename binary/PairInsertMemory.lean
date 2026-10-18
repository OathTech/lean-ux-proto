import PairReplaceMemory
import PairReplaceFields

namespace Binary.Pair.Index
open Leanux Leanux.WG

/-- Concrete hlist_add_head_rcu stores, in the pinned binary's order. The
index scalar has already been written by the draw/store segment. -/
def insertionStores (o : Offsets) (link root first : Nat) : List (Nat×Nat) :=
  [(link+o.pprev,root),(link+o.next,first),(root,link)] ++
    (if first=0 then [] else [(first+o.pprev,link+o.next)])

def insertMemory (m : DataMem) (o : Offsets) (link root first : Nat) : DataMem :=
  write64s m (insertionStores o link root first)

theorem insertion_effect (o : Offsets) (link root first address : Nat) (before : Decode Nat) :
    wordEffect address before (insertionStores o link root first)=
      if first≠0 ∧ address=first+o.pprev then .ok (link+o.next) else
      if address=root then .ok link else
      if address=link+o.next then .ok first else
      if address=link+o.pprev then .ok root else before := by
  by_cases zero : first=0 <;> simp [insertionStores,wordEffect,zero]

/-- A currently unlinked resident entry, independently of any chosen bucket.
These physical facts will be obtained from the executable call assertion and
preserved through the unlink/draw segments. -/
structure UnlinkedEntry (n : Names) (o : Offsets) (m : DataMem) where
  owner : IndexOwner
  base : Nat
  named : (owner,base) ∈ n.owners
  unlinked : word m "owner.pprev" (base+o.hash+o.pprev) 8=.ok 0

namespace UnlinkedEntry
def link {n o m} (f : UnlinkedEntry n o m) : Nat := f.base+o.hash

theorem nonzero {n o m} (f : UnlinkedEntry n o m) (layout : Layout o) : f.link≠0 := by
  simp only [link,layout.hash]
  omega

theorem nextSlot {n o m} (f : UnlinkedEntry n o m) (layout : Layout o) :
    LinkSlot n o (f.link+o.next) := by
  simp only [link,layout.hash,layout.next,Nat.add_zero]
  exact .entry f.owner f.base 8 f.named (.inl rfl)

theorem backSlot {n o m} (f : UnlinkedEntry n o m) (layout : Layout o) :
    LinkSlot n o (f.link+o.pprev) := by
  simp only [link,layout.hash,layout.pprev,Nat.add_assoc]
  exact .entry f.owner f.base 16 f.named (.inr rfl)

theorem absent {n o m b nodes} (f : UnlinkedEntry n o m)
    (layout : Layout o) (table : 0<n.table)
    (shape : Chain n o m b (tableHead n o b) nodes) : f.link ∉ nodes.map Prod.fst := by
  intro member
  obtain ⟨⟨address,entry⟩,present,equal⟩ := List.mem_map.mp member
  change address=f.link at equal
  obtain ⟨prev,next,fields⟩ := shape.member_fields present
  have previous : prev≠0 := by
    rcases shape.back_origin present fields with ⟨atRoot,_⟩ | ⟨parent,current,previous,_,atParent,parentFields⟩
    · rw [atRoot]
      simp only [tableHead,layout.buckets,layout.headSize,layout.first]
      omega
    · rw [←atParent,layout.next]
      simpa using parentFields.nonzero
  have back := fields.back
  rw [equal] at back
  exact previous (word_values back f.unlinked)
end UnlinkedEntry

structure InsertFocus (n : Names) (o : Offsets) (m : DataMem) where
  fresh : UnlinkedEntry n o m
  index : Nat
  indexRead : word m "insert.index" (fresh.base+o.index) 4=.ok index
  kindRead : word m "insert.kind" (fresh.base+o.kind) 4=.ok (ownerKind fresh.owner)
  nodes : Nodes
  shape : Chain n o m (index%8192) (tableHead n o (index%8192)) nodes
  headRead : word m "bucket.head" (tableHead n o (index%8192)) 8=.ok (head nodes)
  distinct : (nodes.map Prod.fst).Nodup

namespace InsertFocus
def root {n o m} (f : InsertFocus n o m) : Nat := tableHead n o (f.index%8192)
def after {n o m} (f : InsertFocus n o m) : DataMem :=
  insertMemory m o f.fresh.link f.root (head f.nodes)

theorem firstSlot {n o m} (f : InsertFocus n o m) (layout : Layout o)
    (nonzero : head f.nodes≠0) : LinkSlot n o (head f.nodes+o.pprev) := by
  cases shape : f.nodes with
  | nil => simp [shape,head] at nonzero
  | cons node rest =>
    have chain := f.shape
    rw [shape] at chain
    cases chain with
    | cons fields tail =>
      simpa only [shape,head,List.head?_cons,Option.map_some,Option.getD_some] using fields.backSlot layout

theorem slots {n o m} (f : InsertFocus n o m) (layout : Layout o)
    (storage : storageCheck n o=true) :
    ∀ address value, (address,value) ∈ insertionStores o f.fresh.link f.root (head f.nodes) →
      LinkSlot n o address ∧ value<2^64 := by
  have bound := entry_bound storage f.fresh.named
  rw [layout.entrySize] at bound
  have rootSlot : LinkSlot n o f.root := .table _ (Nat.mod_lt _ (by decide))
  have rootBound := rootSlot.bounded layout storage
  have linkBound : f.fresh.link+o.next<2^64 := by
    simp only [UnlinkedEntry.link,layout.hash,layout.next]
    omega
  have firstBound := word_bound f.headRead
  intro address value member
  simp only [insertionStores,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with (equal | equal | equal) | member
  · cases equal; exact ⟨f.fresh.backSlot layout,by omega⟩
  · cases equal; exact ⟨f.fresh.nextSlot layout,by simpa using firstBound⟩
  · cases equal; exact ⟨rootSlot,by omega⟩
  · by_cases zero : head f.nodes=0
    · simp [zero] at member
    · have equal : (address,value)=(head f.nodes+o.pprev,f.fresh.link+o.next) := by simpa [zero] using member
      cases equal
      exact ⟨f.firstSlot layout zero,linkBound⟩

theorem read_link {n o m} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (path : String)
    {address : Nat} (slot : LinkSlot n o address) :
    word f.after path address 8=wordEffect address (word m path address 8)
      (insertionStores o f.fresh.link f.root (head f.nodes)) := by
  apply word_write64s _ _ _ _ (slot.bounded layout storage)
  · intro a v member; exact (f.slots layout storage a v member).2
  · intro a v member different
    exact slot.disjoint (f.slots layout storage a v member).1 layout storage different

theorem read_data {n o m} (f : InsertFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) (path : String)
    {address size : Nat} (slot : DataSlot n o address size) :
    word f.after path address size=word m path address size := by
  apply word_write64s_frame
  intro a v member
  exact slot.disjoint_link (f.slots layout storage a v member).1 layout storage

#print axioms read_link
#print axioms read_data
end InsertFocus
end Binary.Pair.Index
