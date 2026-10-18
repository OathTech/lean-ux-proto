import PairReplaceReconstruct

namespace Binary.Pair.Index
open Leanux Leanux.WG
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

theorem targetOwnership_replace (d : Device) (old new : IndexOwner)
    (different : old≠new) (present : d.indexTable.any (·.owner==old)=true) :
    Remove.targetOwnership {d with indexTable := d.indexTable.map (replaceOwner old new)} =
      (Remove.targetOwnership d).map (fun (owner,hashed) =>
        (owner,if owner==old then false else if owner==new then true else hashed)) := by
  have changed (owner : IndexOwner) :
      (d.indexTable.map (replaceOwner old new)).any (·.owner==owner) =
        if owner==old then false else if owner==new then true else d.indexTable.any (·.owner==owner) := by
    by_cases isOld : owner=old
    · subst owner
      simp only [beq_self_eq_true,↓reduceIte]
      apply List.any_eq_false.mpr
      intro e member
      obtain ⟨before,_,rfl⟩ := List.mem_map.mp member
      by_cases same : before.owner=old <;> simp [replaceOwner,same,Ne.symm different]
    · by_cases isNew : owner=new
      · subst owner
        simp only [beq_eq_false_iff_ne.mpr isOld,Bool.false_eq_true,beq_self_eq_true,↓reduceIte]
        obtain ⟨before,member,oldCheck⟩ := List.any_eq_true.mp present
        apply List.any_eq_true.mpr
        refine ⟨replaceOwner old new before,List.mem_map.mpr ⟨before,member,rfl⟩,?_⟩
        simp [replaceOwner,oldCheck]
      · simp only [beq_eq_false_iff_ne.mpr isOld,beq_eq_false_iff_ne.mpr isNew,Bool.false_eq_true,↓reduceIte,List.any_map]
        apply List.any_congr rfl
        intro e
        change ((replaceOwner old new e).owner==owner)=(e.owner==owner)
        by_cases same : e.owner=old
        · simp only [replaceOwner,same,beq_self_eq_true,↓reduceIte,
            beq_eq_false_iff_ne.mpr (Ne.symm isNew),beq_eq_false_iff_ne.mpr (Ne.symm isOld)]
        · simp only [replaceOwner,beq_eq_false_iff_ne.mpr same,Bool.false_eq_true,↓reduceIte]
  simp only [Remove.targetOwnership,List.map_map]
  apply List.map_congr_left
  intro owner _
  simp only [Function.comp_apply,changed]

namespace ReplaceFocus

theorem owners_different {n o m} (f : ReplaceFocus n o m)
    (validated : n.validate o=.ok ()) : f.old.entry.owner≠f.newOwner := by
  obtain ⟨layout,unique,_,_⟩ := validate_basic validated
  intro equal
  have named := f.old.fields.named
  rw [equal] at named
  have bases := unique_first unique named f.named
  have valid := f.old.fields.valid
  exact f.old_different layout (validate_table_positive validated) (by
    change f.old.removed=f.base+o.hash
    omega)

theorem owner_flag {n o m owner base raw} (f : ReplaceFocus n o m)
    (validated : n.validate o=.ok ()) (storage : storageCheck n o=true)
    (named : (owner,base) ∈ n.owners)
    (read : word m "owner.pprev" (base+o.hash+o.pprev) 8=.ok raw) :
    ∃ value, word f.after "owner.pprev" (base+o.hash+o.pprev) 8=.ok value ∧
      (value != 0)=(if owner==f.old.entry.owner then false else if owner==f.newOwner then true else raw != 0) := by
  obtain ⟨layout,ids,addresses,_⟩ := validate_basic validated
  have table := validate_table_positive validated
  have slot : LinkSlot n o (base+o.hash+o.pprev) := by
    simp only [layout.hash,layout.pprev,Nat.add_assoc]
    exact .entry owner base 16 named (.inr rfl)
  have after := f.read_link layout storage "owner.pprev" slot
  rw [replacement_effect] at after
  by_cases oldOwner : owner=f.old.entry.owner
  · have renamed := named
    rw [oldOwner] at renamed
    have bases := unique_first ids renamed f.old.fields.named
    have oldAddress : base+o.hash+o.pprev=f.old.removed+o.pprev := by
      have := f.old.fields.valid
      omega
    refine ⟨0,by simpa only [oldAddress,↓reduceIte] using after,?_⟩
    simp [oldOwner]
  · by_cases newOwner : owner=f.newOwner
    · have renamed := named
      rw [newOwner] at renamed
      have bases := unique_first ids renamed f.named
      refine ⟨f.old.previous,?_,?_⟩
      · rw [bases]
        exact f.new_back layout storage table _
      · simp only [beq_eq_false_iff_ne.mpr oldOwner,beq_iff_eq.mpr newOwner,
          Bool.false_eq_true,↓reduceIte]
        simpa only [bne_iff_ne] using f.old.previous_nonzero layout table
    · have oldBack : base+o.hash+o.pprev≠f.old.removed+o.pprev := by
        intro equal
        have bases : base=f.old.removed-o.hash := by have := f.old.fields.valid; omega
        have renamed := named
        rw [bases] at renamed
        exact oldOwner (unique_second addresses renamed f.old.fields.named)
      have newBack : base+o.hash+o.pprev≠f.link+o.pprev := by
        intro equal
        have bases : base=f.base := by change base+o.hash+o.pprev=f.base+o.hash+o.pprev at equal; omega
        have renamed := named
        rw [bases] at renamed
        exact newOwner (unique_second addresses renamed f.named)
      have otherNext (other : IndexOwner) (otherBase : Nat) (otherNamed : (other,otherBase) ∈ n.owners) :
          base+o.hash+o.pprev≠otherBase+o.hash+o.next := by
        simp only [layout.hash,layout.pprev,layout.next,Nat.add_zero,Nat.add_assoc]
        exact entry_address_ne storage named otherNamed (by rw [layout.entrySize]; decide)
          (by rw [layout.entrySize]; decide) (fun _ => by decide)
      have oldNext : base+o.hash+o.pprev≠f.old.removed+o.next := by
        have same : f.old.removed-o.hash+o.hash=f.old.removed := Nat.sub_add_cancel f.old.fields.valid
        simpa only [same] using otherNext _ _ f.old.fields.named
      have newNext : base+o.hash+o.pprev≠f.link+o.next := otherNext _ _ f.named
      have previous := f.old.owner_back_ne_previous named layout storage
      simp only [oldBack,oldNext,newBack,newNext,previous,↓reduceIte,read] at after
      by_cases successor : f.old.next≠0 ∧ base+o.hash+o.pprev=f.old.next+o.pprev
      · obtain ⟨entry,next,fields⟩ := f.old.nextFields successor.1
        have oldRead := read
        rw [successor.2] at oldRead
        have oldValue := word_values oldRead fields.back
        have rawNonzero : raw≠0 := by rw [oldValue,layout.next]; simpa using f.old.fields.nonzero
        have newNonzero : f.link+o.next≠0 := by rw [layout.next]; simpa using f.nonzero layout
        refine ⟨f.link+o.next,by rw [ite_eq_left successor] at after; exact after,?_⟩
        simp only [beq_eq_false_iff_ne.mpr oldOwner,beq_eq_false_iff_ne.mpr newOwner,
          Bool.false_eq_true,↓reduceIte,
          show (raw != 0)=true from by simpa only [bne_iff_ne] using rawNonzero,
          show (f.link+o.next != 0)=true from by simpa only [bne_iff_ne] using newNonzero]
      · refine ⟨raw,by simpa only [successor,↓reduceIte] using after,?_⟩
        simp [oldOwner,newOwner]

theorem ownership {n o m d} (f : ReplaceFocus n o m)
    (related : Corresponds n o m d) (storage : storageCheck n o=true)
    (owned : Remove.ownership n o m=.ok (Remove.targetOwnership d))
    (present : d.indexTable.any (·.owner==f.old.entry.owner)=true) :
    Remove.ownership n o f.after=.ok
      (Remove.targetOwnership {d with indexTable := d.indexTable.map (replaceOwner f.old.entry.owner f.newOwner)}) := by
  have validated := (reconstruct_components related).1
  rw [targetOwnership_replace d _ _ (f.owners_different validated) present]
  have mapped := mapM_ok owned
  have changed : Remove.ownership n o f.after=(Remove.ownership n o m).map
      (List.map (fun (owner,hashed) =>
        (owner,if owner==f.old.entry.owner then false else if owner==f.newOwner then true else hashed))) := by
    unfold Remove.ownership
    rw [←Trie.mapM_map_result]
    apply Trie.mapM_same
    rintro ⟨owner,base⟩ named
    obtain ⟨value,_,decoded⟩ := mapped.left (owner,base) named
    obtain ⟨raw,read,_⟩ := bind_ok decoded
    obtain ⟨updated,newRead,flag⟩ := f.owner_flag validated storage named read
    dsimp only
    rw [newRead,read]
    change Except.ok (owner,updated != 0)=Except.ok
      (owner,if owner==f.old.entry.owner then false else if owner==f.newOwner then true else raw != 0)
    rw [flag]
  rw [changed,owned]
  rfl

#print axioms ownership
end ReplaceFocus
end Binary.Pair.Index
