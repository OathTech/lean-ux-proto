import PairInsertUnhashBody
import PairInsertGuard
import PairInsertResident

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

theorem Core.rebase {n o c initial ra p shadow s} (core : Core n o c initial ra p shadow s) :
    Core n o c initial ra p s.dmem s :=
  ⟨core.stack,core.table,core.owner,core.memory,fun _ _ _ _ => rfl⟩

def UnhashPost (n : Names) (o : Offsets) (c : Context) (initial : MachineState)
    (ra : UInt64) (d : Device) (owner : IndexOwner) (base : Nat) (t : MachineState) : Prop :=
  let unlinked := {d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))}
  t.pc=codeEntry+0x4f ∧ Core n o c initial ra .outer t.data.dmem t.data ∧
    Corresponds n o t.data.dmem unlinked ∧
    Remove.ownership n o t.data.dmem=.ok (Remove.targetOwnership unlinked) ∧
    Resident n o t.data.dmem owner base ∧ word t.data.dmem "owner.pprev" (base+o.hash+o.pprev) 8=.ok 0

/-- Both initial linkage branches establish the same actual-memory boundary.
No future retry result or later precondition is an entry assumption. -/
theorem unhash_entry (fetch : Int64 → Option Decoded) (decoder : IndexInsertDecoderAgreement fetch)
    (trace : TracePcContract fetch) {n o c initial ra d owner base}
    (facts : FrameFacts n o c initial ra) (related : Corresponds n o initial.data.dmem d)
    (storage : storageCheck n o=true)
    (owners : Remove.ownership n o initial.data.dmem=.ok (Remove.targetOwnership d))
    (resident : Resident n o initial.data.dmem owner base)
    (argument : initial.data.regs.rsi.toNat=base) (entryPc : initial.pc=codeEntry) :
    Eventually (instructionStep fetch) (UnhashPost n o c initial ra d owner base) initial := by
  obtain ⟨layout,unique,_⟩ := validate_basic (reconstruct_components related).1
  obtain ⟨previous,read,flag⟩ := Remove.ownership_flag owners resident.named
  have previousBound := word_bound read
  have wordRead := word_loadInt _ _ _ _ _ read
  rw [layout.hash,layout.pprev] at wordRead
  have physicalRead : initial.data.dmem.loadInt (.ofNat 64 (base+16)) 8=some ((BitVec.ofNat 64 previous).toNat : Int) := by
    simpa only [Nat.add_assoc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt previousBound] using wordRead
  have entered := start fetch decoder trace facts entryPc
  apply eventually_trans (instructionStep fetch) _ _ _ entered
  rintro started ⟨pc,core⟩
  have guard := disable_unhash fetch decoder facts core layout resident.named argument (.ofNat 64 previous) physicalRead
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc guard)
  rintro guarded ⟨pc,core,bx⟩
  by_cases zero : previous=0
  · have unhashed : d.indexTable.any (·.owner==owner)=false := by simpa [zero] using flag.symm
    have filter : d.indexTable.filter (fun e => !(e.owner==owner))=d.indexTable := by
      apply List.filter_eq_self.mpr
      intro e member
      have absent := List.any_eq_false.mp unhashed e member
      simp only [absent,Bool.not_false]
    have updated : ({d with indexTable := d.indexTable.filter (fun e => !(e.owner==owner))} : Device)=d := by rw [filter]
    apply Eventually.done
    dsimp only [UnhashPost]
    rw [updated]
    refine ⟨by simpa [zero] using pc,core.rebase,core.frame.reconstruct related,?_,resident.frame layout core.frame,?_⟩
    · rw [←core.frame.ownership layout]
      exact owners
    · have same := core.frame.word (entry_storage resident.named) (o.hash+o.pprev) 8
        (by rw [layout.hash,layout.pprev,layout.entrySize]; omega) "owner.pprev"
      rw [←Nat.add_assoc] at same
      rw [←same]
      simpa only [zero] using read
  · have different : (previous != 0 : Bool)=true := by simpa only [bne_iff_ne] using zero
    have hashed : d.indexTable.any (·.owner==owner)=true := flag.symm.trans different
    obtain ⟨entry,member,ownerCheck⟩ := List.any_eq_true.mp hashed
    have ownerEq : entry.owner=owner := eq_of_beq ownerCheck
    obtain ⟨f,entryEq⟩ := reconstruct_focus related member
    have focusOwner : f.entry.owner=owner := by rw [entryEq]; exact ownerEq
    have focusNamed : (owner,f.removed-o.hash) ∈ n.owners := by rw [←focusOwner]; exact f.fields.named
    have baseEq := unique_first unique resident.named focusNamed
    have removed : f.removed=base+8 := by have valid := f.fields.valid; rw [layout.hash] at baseEq valid; omega
    have prevEq : previous=f.previous := by
      have focusRead := f.fields.back
      rw [removed] at focusRead
      rw [layout.hash] at read
      exact word_values read focusRead
    have initialArg : initial.data.regs.rsi.toBitVec=BitVec.ofNat 64 base := by
      apply BitVec.eq_of_toNat_eq
      simp only [UInt64.toNat_toBitVec,BitVec.toNat_ofNat,←argument,Nat.mod_eq_of_lt initial.data.regs.rsi.toNat_lt_size]
    have cursor : initial.data.regs.rsi.toBitVec+8=BitVec.ofNat 64 f.removed := by
      rw [initialArg,removed,BitVec.ofNat_add]
      rfl
    have nonzero : BitVec.ofNat 64 previous≠0 := by
      intro equal
      apply zero
      have values := congrArg BitVec.toNat equal
      simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt previousBound] using values
    rw [ite_eq_right nonzero] at pc
    have splice := unhash_body fetch decoder trace facts core layout f cursor (by rw [bx,prevEq])
    apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc splice)
    rintro unlinked ⟨pc,core⟩
    have reconstructed := core.frame.reconstruct (f.reconstruct related storage)
    have owned := (core.frame.ownership layout).symm.trans (f.ownership (reconstruct_components related).1 storage owners)
    rw [focusOwner] at reconstructed owned
    refine ⟨pc,core.rebase,reconstructed,owned,(resident.unhash layout storage f).frame layout core.frame,?_⟩
    have cleared : word (unlinkMemory initial.data.dmem o f.removed f.previous f.next)
        "owner.pprev" (base+o.hash+o.pprev) 8=.ok 0 := by
      have slot : LinkSlot n o (base+o.hash+o.pprev) := by
        rw [layout.hash,layout.pprev,show base+8+8=base+16 by omega]
        exact .entry owner base 16 resident.named (.inr rfl)
      have effect := f.read_link layout storage "owner.pprev" slot
      have equal : base+o.hash+o.pprev=f.removed+o.pprev := by rw [removed,layout.hash]
      simpa only [equal,↓reduceIte] using effect
    have same := core.frame.word (entry_storage resident.named) (o.hash+o.pprev) 8
      (by rw [layout.hash,layout.pprev,layout.entrySize]; omega) "owner.pprev"
    rw [←Nat.add_assoc] at same
    exact same.symm.trans cleared

#print axioms unhash_entry
end Binary.Pair.Insert
