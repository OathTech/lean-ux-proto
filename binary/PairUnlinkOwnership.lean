import PairUnlinkReconstruct
import PairRemoveOwnership

namespace Binary.Pair.Index
open Leanux Leanux.WG
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

theorem unique_second {α β : Type} {pairs : List (α×β)}
    (unique : (pairs.map Prod.snd).Nodup) {a b : α} {address : β}
    (left : (a,address) ∈ pairs) (right : (b,address) ∈ pairs) : a=b := by
  have identity : (Prod.fst ∘ Prod.swap : α×β → β)=Prod.snd := rfl
  have swapped : ((pairs.map Prod.swap).map Prod.fst).Nodup := by
    simpa only [List.map_map,identity] using unique
  exact unique_first swapped
    (List.mem_map.mpr ⟨(a,address),left,rfl⟩) (List.mem_map.mpr ⟨(b,address),right,rfl⟩)

theorem validate_table_positive {n o} (checked : Names.validate n o=.ok ()) : 0<n.table := by
  unfold Names.validate at checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨range,_⟩ := check_ok _ _ _ _ checked
  exact (show 0<n.table ∧ n.table+o.tableSize<2^64 from by simpa using range).1

namespace UnlinkFocus

theorem previous_nonzero {n o m} (f : UnlinkFocus n o m)
    (layout : Layout o) (table : 0<n.table) : f.previous≠0 := by
  rcases f.shape.back_origin f.member f.fields with ⟨atRoot,_⟩ | ⟨parent,current,prev,_,address,parentFields⟩
  · rw [atRoot]
    simp only [tableHead,layout.buckets,layout.headSize,layout.first]
    omega
  · rw [←address,layout.next]
    simpa using parentFields.nonzero

theorem owner_back_ne_previous {n o m owner base} (f : UnlinkFocus n o m)
    (named : (owner,base) ∈ n.owners)
    (layout : Layout o) (storage : storageCheck n o=true) : base+o.hash+o.pprev≠f.previous := by
  have slot : base+o.hash+o.pprev=base+16 := by rw [layout.hash,layout.pprev]
  rw [slot]
  rcases f.shape.back_origin f.member f.fields with ⟨atRoot,_⟩ | ⟨parent,current,prev,_,address,parentFields⟩
  · rw [atRoot]
    exact Ne.symm (table_entry_ne layout storage named (by rw [layout.entrySize]; decide) f.validBucket)
  · rw [←address]
    have parentAddress : parent-o.hash+8=parent+o.next := by
      have := parentFields.valid
      rw [layout.hash,layout.next] at *
      omega
    rw [←parentAddress]
    apply address_ne_of_disjoint
    exact entry_fields_apart storage named parentFields.named
      (by rw [layout.entrySize]; decide) (by rw [layout.entrySize]; decide) (fun _ => by decide)

theorem owner_flag {n o m owner base raw} (f : UnlinkFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true)
    (named : (owner,base) ∈ n.owners)
    (read : word m "owner.pprev" (base+o.hash+o.pprev) 8=.ok raw) :
    ∃ value, word (unlinkMemory m o f.removed f.previous f.next) "owner.pprev" (base+o.hash+o.pprev) 8=.ok value ∧
      (value != 0)=(if owner==f.entry.owner then false else raw != 0) := by
  obtain ⟨layout,ids,addresses,_⟩ := validate_basic validated
  have slot : LinkSlot n o (base+o.hash+o.pprev) := by
    have address : base+o.hash+o.pprev=base+16 := by rw [layout.hash,layout.pprev]
    rw [address]
    exact .entry owner base 16 named (.inr rfl)
  have after := f.read_link layout storage "owner.pprev" slot
  by_cases same : owner=f.entry.owner
  · have renamed := named
    rw [same] at renamed
    have equal := unique_first ids renamed f.fields.named
    have cleared : base+o.hash+o.pprev=f.removed+o.pprev := by
      have := f.fields.valid
      omega
    refine ⟨0,?_,by simp [same]⟩
    simpa only [cleared,↓reduceIte] using after
  · have notCleared : base+o.hash+o.pprev≠f.removed+o.pprev := by
      intro equal
      have bases : base=f.removed-o.hash := by
        have := f.fields.valid
        omega
      have renamed := named
      rw [bases] at renamed
      exact same (unique_second addresses renamed f.fields.named)
    have notPrevious := f.owner_back_ne_previous named layout storage
    simp only [notCleared,↓reduceIte,notPrevious,read] at after
    by_cases successor : f.next≠0 ∧ base+o.hash+o.pprev=f.next+o.pprev
    · obtain ⟨entry,next,fields⟩ := f.nextFields successor.1
      have previousRead := read
      rw [successor.2] at previousRead
      have oldValue : raw=f.removed+o.next := word_values previousRead fields.back
      have oldNonzero : raw≠0 := by rw [oldValue,layout.next]; simpa using f.fields.nonzero
      have newNonzero := f.previous_nonzero layout (validate_table_positive validated)
      refine ⟨f.previous,by rw [ite_eq_left successor] at after; exact after,?_⟩
      simp only [beq_eq_false_iff_ne.mpr same,Bool.false_eq_true,↓reduceIte,
        show (raw != 0)=true from by simpa using oldNonzero,
        show (f.previous != 0)=true from by simpa using newNonzero]
    · refine ⟨raw,by simpa only [successor,↓reduceIte] using after,?_⟩
      simp [same]

theorem ownership {n o m d} (f : UnlinkFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true)
    (related : Remove.ownership n o m=.ok (Remove.targetOwnership d)) :
    Remove.ownership n o (unlinkMemory m o f.removed f.previous f.next)=
      .ok (Remove.targetOwnership {d with indexTable := d.indexTable.filter (fun e => !(e.owner==f.entry.owner))}) := by
  rw [Remove.targetOwnership_remove]
  have mapped := mapM_ok related
  have changed : Remove.ownership n o (unlinkMemory m o f.removed f.previous f.next)=
      (Remove.ownership n o m).map
        (List.map (fun (owner,hashed) => (owner,if owner==f.entry.owner then false else hashed))) := by
    unfold Remove.ownership
    rw [←Trie.mapM_map_result]
    apply Trie.mapM_same
    rintro ⟨owner,base⟩ named
    obtain ⟨value,_,decoded⟩ := mapped.left (owner,base) named
    obtain ⟨raw,read,_⟩ := bind_ok decoded
    obtain ⟨updated,newRead,flag⟩ := f.owner_flag validated storage named read
    dsimp only
    rw [newRead,read]
    change Except.ok (owner,updated != 0)=Except.ok (owner,if owner==f.entry.owner then false else raw != 0)
    rw [flag]
  rw [changed,related]
  rfl

#print axioms ownership
end UnlinkFocus
end Binary.Pair.Index
