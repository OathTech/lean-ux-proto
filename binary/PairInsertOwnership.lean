import PairInsertIndex
import PairReplaceOwnership

namespace Binary.Pair.Index
open Leanux Leanux.WG
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

theorem UnlinkedEntry.draw_ownership {n o m} (f : UnlinkedEntry n o m) (value : Nat)
    (layout : Layout o) (storage : storageCheck n o=true) :
    Remove.ownership n o (f.afterDraw value)=Remove.ownership n o m := by
  apply Trie.mapM_same
  rintro ⟨owner,base⟩ named
  have slot : LinkSlot n o (base+o.hash+o.pprev) := by
    simp only [layout.hash,layout.pprev,Nat.add_assoc]
    exact .entry owner base 16 named (.inr rfl)
  simp only [f.draw_link value layout storage slot]

theorem targetOwnership_insert (d : Device) (entry : IndexEntry) :
    Remove.targetOwnership {d with indexTable := entry::d.indexTable}=
      (Remove.targetOwnership d).map (fun (owner,hashed) =>
        (owner,if owner==entry.owner then true else hashed)) := by
  simp only [Remove.targetOwnership,List.map_map]
  apply List.map_congr_left
  intro owner _
  simp only [Function.comp_apply,List.any_cons]
  by_cases same : owner=entry.owner
  · simp [same]
  · simp [same,Ne.symm same]

namespace InsertFocus
theorem owner_flag {n o m owner base raw} (f : InsertFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true)
    (named : (owner,base) ∈ n.owners)
    (read : word m "owner.pprev" (base+o.hash+o.pprev) 8=.ok raw) :
    ∃ value, word f.after "owner.pprev" (base+o.hash+o.pprev) 8=.ok value ∧
      (value != 0)=(if owner==f.fresh.owner then true else raw != 0) := by
  obtain ⟨layout,ids,addresses,_⟩ := validate_basic validated
  have table := validate_table_positive validated
  have slot : LinkSlot n o (base+o.hash+o.pprev) := by
    simp only [layout.hash,layout.pprev,Nat.add_assoc]
    exact .entry owner base 16 named (.inr rfl)
  by_cases same : owner=f.fresh.owner
  · have renamed := named
    rw [same] at renamed
    have baseEq := unique_first ids renamed f.fresh.named
    refine ⟨f.root,?_,?_⟩
    · rw [baseEq]
      exact f.new_back layout storage table _
    · have nonzero : f.root≠0 := by
        simp only [root,tableHead,layout.buckets,layout.headSize,layout.first]
        omega
      simp [same,nonzero]
  · have newBack : base+o.hash+o.pprev≠f.fresh.link+o.pprev := by
      intro equal
      have baseEq : base=f.fresh.base := by
        change base+o.hash+o.pprev=f.fresh.base+o.hash+o.pprev at equal
        omega
      have renamed := named
      rw [baseEq] at renamed
      exact same (unique_second addresses renamed f.fresh.named)
    have newNext : base+o.hash+o.pprev≠f.fresh.link+o.next := by
      simp only [UnlinkedEntry.link,layout.hash,layout.pprev,layout.next,Nat.add_zero,Nat.add_assoc]
      exact entry_address_ne storage named f.fresh.named (by rw [layout.entrySize]; decide)
        (by rw [layout.entrySize]; decide) (fun _ => by decide)
    have rootNe : base+o.hash+o.pprev≠f.root := by
      have separate := table_entry_ne layout storage named (offset := 16)
        (by rw [layout.entrySize]; decide) (Nat.mod_lt f.index (by decide))
      simpa only [root,layout.hash,layout.pprev,Nat.add_assoc] using Ne.symm separate
    have after := f.read_link layout storage "owner.pprev" slot
    rw [insertion_effect] at after
    simp only [newBack,newNext,rootNe,↓reduceIte,read] at after
    by_cases first : head f.nodes≠0 ∧ base+o.hash+o.pprev=head f.nodes+o.pprev
    · obtain ⟨entry,next,fields⟩ := f.firstFields first.1
      have oldRead := read
      rw [first.2] at oldRead
      have rawEq := word_values oldRead fields.back
      have rawNonzero : raw≠0 := by
        rw [rawEq]
        simp only [root,tableHead,layout.buckets,layout.headSize,layout.first]
        omega
      have newNonzero : f.fresh.link+o.next≠0 := by
        rw [layout.next,Nat.add_zero]
        exact f.fresh.nonzero layout
      exact ⟨f.fresh.link+o.next,by rw [ite_eq_left first] at after; exact after,
        by rw [bne_iff_ne.mpr rawNonzero,bne_iff_ne.mpr newNonzero]; simp [same]⟩
    · exact ⟨raw,by rw [ite_eq_right first] at after; exact after,by simp [same]⟩

theorem ownership {n o m d} (f : InsertFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true)
    (related : Remove.ownership n o m=.ok (Remove.targetOwnership d)) :
    Remove.ownership n o f.after=.ok (Remove.targetOwnership
      {d with indexTable := ⟨f.index,f.fresh.owner⟩::d.indexTable}) := by
  rw [targetOwnership_insert]
  have mapped := mapM_ok related
  have changed : Remove.ownership n o f.after=(Remove.ownership n o m).map
      (List.map fun (owner,hashed) => (owner,if owner==f.fresh.owner then true else hashed)) := by
    unfold Remove.ownership
    rw [←Trie.mapM_map_result]
    apply Trie.mapM_same
    rintro ⟨owner,base⟩ named
    obtain ⟨result,_,read⟩ := mapped.left (owner,base) named
    obtain ⟨raw,loaded,_⟩ := bind_ok read
    obtain ⟨value,updated,flag⟩ := f.owner_flag validated storage named loaded
    simp only [updated,loaded]
    change Except.ok (owner,value != 0)=Except.ok (owner,if owner==f.fresh.owner then true else raw != 0)
    rw [flag]
  rw [changed,related]
  rfl

#print axioms ownership
end InsertFocus
end Binary.Pair.Index
