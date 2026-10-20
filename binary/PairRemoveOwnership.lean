import PairRemoveRegion
import PairCountUpdate

namespace Binary.Pair.Remove
open Leanux Leanux.WG
local instance : Labels := Image.linkedLabels
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by
    intro a b h
    cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

/-- The ownership part of the tested abstraction after the actual source's
index-table filter. No physical pointer is supplied by this projection. -/
theorem targetOwnership_remove (d : Device) (removed : IndexOwner) :
    targetOwnership {d with indexTable := d.indexTable.filter (fun e => !(e.owner==removed))} =
      (targetOwnership d).map (fun (owner,hashed) =>
        (owner,if owner==removed then false else hashed)) := by
  have changed (owner : IndexOwner) :
      (d.indexTable.filter (fun e => !(e.owner==removed))).any (·.owner==owner) =
        if owner==removed then false else d.indexTable.any (·.owner==owner) := by
    induction d.indexTable with
    | nil => simp
    | cons e rest ih =>
      by_cases hr : e.owner=removed <;> by_cases ho : e.owner=owner <;>
        by_cases same : owner=removed <;> simp_all
  simp only [targetOwnership,List.map_map]
  apply List.map_congr_left
  intro owner _
  simp only [Function.comp_apply,changed]

/-- Decode all owner flags after a concrete memory effect. The only changed
word is the removed owner's pprev; all other flag reads follow the frame. -/
theorem ownership_update (n : Names) (o : Offsets) (before after : DataMem)
    (d : Device) (removed : IndexOwner)
    (related : ownership n o before = .ok (targetOwnership d))
    (changed : ∀ base, (removed,base) ∈ n.owners →
      word after "owner.pprev" (base+o.hash+o.pprev) 8=.ok 0)
    (others : ∀ owner base, (owner,base) ∈ n.owners → owner≠removed →
      word after "owner.pprev" (base+o.hash+o.pprev) 8 =
        word before "owner.pprev" (base+o.hash+o.pprev) 8) :
    ownership n o after = .ok (targetOwnership
      {d with indexTable := d.indexTable.filter (fun e => !(e.owner==removed))}) := by
  rw [targetOwnership_remove]
  have mapped := mapM_ok related
  have transformed : ownership n o after = (ownership n o before).map
      (List.map (fun (owner,hashed) => (owner,if owner==removed then false else hashed))) := by
    unfold ownership
    rw [←Trie.mapM_map_result]
    apply Trie.mapM_same
    rintro ⟨owner,base⟩ member
    obtain ⟨value,_,read⟩ := mapped.left (owner,base) member
    obtain ⟨raw,loaded,_⟩ := bind_ok read
    by_cases same : owner=removed
    · subst owner
      simp only [changed base member,loaded]
      change Except.ok (removed,false) = Except.ok
        (removed,if removed==removed then false else raw != 0)
      simp
    · simp only [others owner base member same,loaded]
      change Except.ok (owner,raw != 0) = Except.ok
        (owner,if owner==removed then false else raw != 0)
      simp [same]
  rw [transformed,related]
  rfl

/-- A fresh binary segment establishes the same executable ownership update
checked by the runner. Bucket-list reconstruction is a separate, still-open
obligation for the complete unlink; this theorem does not assume it as a fact. -/
theorem clear_ownership (s : MachineData) (n : Names) (o : Offsets)
    (d : Device) (removed : IndexOwner) (base : Nat)
    (named : (removed,base) ∈ n.owners)
    (unique : ∀ other, (removed,other) ∈ n.owners → other=base)
    (layout : o.hash+o.pprev=16)
    (register : s.regs.rbx.toBitVec=.ofNat 64 base)
    (bounded : base+24≤2^64)
    (related : ownership n o s.dmem = .ok (targetOwnership d))
    (apart : ∀ owner addr, (owner,addr) ∈ n.owners → owner≠removed →
      ∀ a, InRange (.ofNat 64 (addr+o.hash+o.pprev)) 8 a →
        ¬InRange (.ofNat 64 (base+16)) 8 a) :
    Eventually (instructionStep clearFetch) (fun t =>
      t.pc=clearPC+8 ∧ t.data.regs=s.regs ∧
      ownership n o t.data.dmem = .ok (targetOwnership
        {d with indexTable := d.indexTable.filter (fun e => !(e.owner==removed))}) ∧
      EqualOutside (InRange (.ofNat 64 (base+16)) 8) s.dmem t.data.dmem) ⟨s,clearPC⟩ := by
  obtain ⟨value,_,read⟩ := (mapM_ok related).left (removed,base) named
  obtain ⟨raw,loaded,_⟩ := bind_ok read
  have address : s.regs.rbx.toBitVec+16 = .ofNat 64 (base+o.hash+o.pprev) := by
    rw [register,Nat.add_assoc,layout]
    simp only [BitVec.ofNat_add]
    rfl
  have physical := word_loadInt _ _ _ _ _ loaded
  rw [←address] at physical
  have run := clear_effect s _ physical
  apply eventually_weaken (instructionStep clearFetch) _ _ _ _ run
  rintro t ⟨pc,regs,zero,frame⟩
  have addr16 : s.regs.rbx.toBitVec+16 = .ofNat 64 (base+16) := by
    rw [register]; simp only [BitVec.ofNat_add]; rfl
  rw [addr16] at frame
  refine ⟨pc,regs,ownership_update n o s.dmem t.data.dmem d removed related ?_ ?_,frame⟩
  · intro other member
    rw [unique other member]
    apply Trie.word_of_loadInt
    · omega
    · simpa only [address,Int.natCast_zero] using zero
  · intro owner addr member different
    exact (Trie.word_frame frame "owner.pprev" _ _ (apart owner addr member different)).symm

#print axioms clear_ownership
end Binary.Pair.Remove
