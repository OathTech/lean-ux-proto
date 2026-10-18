import PairReplaceBody
import PairReplaceFinish
import PairReplaceSource

namespace Binary.Pair.Replace
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
local instance : Labels := Image.linkedLabels
local instance : LawfulBEq IndexOwner where
  eq_of_beq := by intro a b h; cases a <;> cases b <;> simp_all [BEq.beq,instBEqIndexOwner.beq]
  rfl := by intro a; cases a <;> simp [BEq.beq,instBEqIndexOwner.beq]

theorem replace_heap_frame {n o m} (f : ReplaceFocus n o m)
    (layout : Layout o) (storage : storageCheck n o=true) :
    EqualOutside (HeapBytes n o) m f.after := by
  have indexSlot : DataSlot n o (f.base+28) 4 := .entry f.newOwner f.base 28 4 f.named (.inr (.inr rfl))
  have address : f.link-o.hash+o.index=f.base+28 := by simp only [ReplaceFocus.link,Nat.add_sub_cancel,layout.index]
  have first := storeInt_frame m (.ofNat 64 (f.base+28)) 4 (BitVec.ofNat 32 f.old.entry.index).toInt
  have rest := write64s_frame (write32 m (f.link-o.hash+o.index) f.old.entry.index)
    (replacementStores o f.old.removed f.link f.old.previous f.old.next)
  intro a outside
  have before := first a (fun inside => outside (indexSlot.heap layout a inside))
  rw [←address] at before
  exact before.trans (rest a (by
    rintro ⟨destination,value,member,inside⟩
    have slot := (replacement_slots f.old layout storage f.named rfl destination value member).1
    exact outside (slot.heap layout a inside)))

def Post (n : Names) (o : Offsets) (c : Context) (initial : MachineState)
    (ra : UInt64) (answer : Bool) (final : World) (t : MachineState) : Prop :=
  Returned initial t ra ∧ t.data.regs.rax.toBitVec.setWidth 8=(if answer then (1 : BitVec 8) else 0) ∧
    MemoryReady c initial ra 5 (savedWords initial.data) false t.data.dmem ∧
    (∃ d, final.k.wg=some d ∧ Corresponds n o t.data.dmem d ∧
      Remove.ownership n o t.data.dmem=.ok (Remove.targetOwnership d)) ∧
    EqualOutside (fun a => HeapBytes n o a ∨ External c initial 5 a) initial.data.dmem t.data.dmem

/-- Complete sequential replacement from the tested entry assertion. The
new entry's readiness is conditional on old membership, exactly as checked. -/
theorem replace_checked (fetch : Int64 → Option Decoded) (decoder : IndexReplaceDecoderAgreement fetch)
    (trace : TracePcContract fetch) (bh : BhEnableContract fetch)
    {n o c initial w pid kid ra answer final} (checked : Pre n o c initial w pid kid ra)
    (accepted : (WG.indexReplaceHandshake pid kid).run w=.ok (answer,final)) :
    Eventually (instructionStep fetch) (Post n o c initial ra answer final) initial := by
  obtain ⟨d,old,new,device,related,storage,owned,oldNamed,newNamed,pc,oldArg,newArg,facts,newReady⟩ := pre_facts checked
  have validated := (reconstruct_components related).1
  obtain ⟨layout,unique,_,_⟩ := validate_basic validated
  obtain ⟨answerEq,finalEq⟩ := source_effect device accepted
  obtain ⟨previous,read,flag⟩ := Remove.ownership_flag owned oldNamed
  have previousBound := word_bound read
  have physicalRead : initial.data.dmem.loadInt (.ofNat 64 (old+16)) 8=some ((BitVec.ofNat 64 previous).toNat : Int) := by
    have raw := word_loadInt _ _ _ _ _ read
    simpa only [layout.hash,layout.pprev,Nat.add_assoc,BitVec.toNat_ofNat,Nat.mod_eq_of_lt previousBound] using raw
  have entryPc : initial.pc=codeEntry := by
    apply Int64.toBitVec_inj.mp
    apply BitVec.eq_of_toNat_eq
    exact pc
  have entered := start fetch decoder trace facts entryPc
  apply eventually_trans (instructionStep fetch) _ _ _ entered
  rintro started ⟨pc,core⟩
  have guard := disable fetch decoder facts core layout oldNamed oldArg (.ofNat 64 previous) physicalRead
  apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc guard)
  rintro guarded ⟨pc,core⟩
  have zeroIff : BitVec.ofNat 64 previous=0 ↔ previous=0 := by
    constructor
    · intro equal
      have values := congrArg BitVec.toNat equal
      simpa [BitVec.toNat_ofNat,Nat.mod_eq_of_lt previousBound] using values
    · intro equal; simp [equal]
  by_cases zero : previous=0
  · have hashed : sourceAnswer d pid=false := by simpa [sourceAnswer,zero] using flag.symm
    have atTail : guarded.pc=codeEntry+0x81 := by
      rw [ite_eq_left (zeroIff.mpr zero)] at pc
      exact pc
    have tail := finish fetch decoder trace bh facts core
    apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc atTail tail)
    rintro t ⟨returned,ready,frame,result⟩
    have heap := external_storage facts.geometry frame
    refine ⟨returned,?_,ready,⟨d,?_,heap.reconstruct related,?_⟩,?_⟩
    · rw [result,result_low,answerEq,hashed,ite_eq_left (zeroIff.mpr zero)]
      rfl
    · rw [finalEq]
      change some (if sourceAnswer d pid then _ else d)=some d
      rw [hashed]
      rfl
    · rw [←heap.ownership layout]
      exact owned
    · intro a outside
      exact frame a (fun inside => outside (.inr inside))
  · have hashed : sourceAnswer d pid=true := by
      simpa only [sourceAnswer,bne_iff_ne] using flag.symm.trans (by simpa only [bne_iff_ne] using zero)
    have ready := newReady hashed
    obtain ⟨entry,member,ownerCheck⟩ := List.any_eq_true.mp hashed
    have ownerEq : entry.owner=.handshake pid := eq_of_beq ownerCheck
    obtain ⟨focus,focusEntry⟩ := reconstruct_focus related member
    have owner : focus.entry.owner=.handshake pid := by rw [focusEntry]; exact ownerEq
    have focusNamed : (.handshake pid,focus.removed-o.hash) ∈ n.owners := by rw [←owner]; exact focus.fields.named
    have oldBase := unique_first unique oldNamed focusNamed
    obtain ⟨newPrevious,newRead,newFlag⟩ := Remove.ownership_flag owned newNamed
    have newZero : newPrevious=0 := by
      rw [ready.absent] at newFlag
      simpa using newFlag
    have unlinked : word initial.data.dmem "owner.pprev" (new+o.hash+o.pprev) 8=.ok 0 := by
      simpa only [newZero] using newRead
    let f : ReplaceFocus n o initial.data.dmem := ⟨focus,.keypair kid,new,newNamed,ready.kind,unlinked⟩
    have oldRegister : initial.data.regs.rsi.toBitVec=BitVec.ofNat 64 (f.old.removed-o.hash) := by
      change initial.data.regs.rsi.toBitVec=BitVec.ofNat 64 (focus.removed-o.hash)
      rw [←oldBase,←oldArg]
      simp only [←UInt64.toNat_toBitVec,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    have newRegister : initial.data.regs.rdx.toBitVec=BitVec.ofNat 64 f.base := by
      apply BitVec.eq_of_toNat_eq
      simp only [UInt64.toNat_toBitVec,BitVec.toNat_ofNat,show f.base=new from rfl,←newArg,
        Nat.mod_eq_of_lt initial.data.regs.rdx.toNat_lt_size]
    have nextMapped : (initial.data.dmem.loadInt (.ofNat 64 (f.base+8)) 8).isSome=true := by
      obtain ⟨value,read⟩ := ready.next
      have raw := word_loadInt _ _ _ _ _ read
      simp only [layout.hash,layout.next,Nat.add_zero] at raw
      rw [raw]
      rfl
    have indexMapped : (initial.data.dmem.loadInt (.ofNat 64 (f.base+28)) 4).isSome=true := by
      obtain ⟨value,read⟩ := ready.index
      have raw := word_loadInt _ _ _ _ _ read
      rw [layout.index] at raw
      rw [raw]
      rfl
    rw [ite_eq_right (fun equal => zero (zeroIff.mp equal))] at pc
    have mutation := body fetch decoder trace facts core validated storage f oldRegister newRegister nextMapped indexMapped
    apply eventually_trans (instructionStep fetch) _ _ _ (at_pc pc mutation)
    rintro mutated ⟨pc,core⟩
    have tail := finish fetch decoder trace bh facts core
    apply eventually_weaken (instructionStep fetch) _ _ _ _ (at_pc pc tail)
    rintro t ⟨returned,ready,frame,result⟩
    have heap := external_storage facts.geometry frame
    have oldPresent : d.indexTable.any (·.owner==f.old.entry.owner)=true := by rw [show f.old.entry.owner=.handshake pid from owner]; exact hashed
    refine ⟨returned,?_,ready,⟨_,?_,heap.reconstruct (f.reconstruct related storage),?_⟩,
      (replace_heap_frame f layout storage).trans frame⟩
    · rw [result,result_low,answerEq,hashed,ite_eq_right (fun equal => zero (zeroIff.mp equal))]
      rfl
    · rw [finalEq]
      change some (if sourceAnswer d pid then _ else d)=some _
      rw [hashed]
      change some {d with indexTable := d.indexTable.map (replaceOwner (.handshake pid) (.keypair kid))}=
        some {d with indexTable := d.indexTable.map (replaceOwner f.old.entry.owner f.newOwner)}
      rw [show f.old.entry.owner=.handshake pid from owner]
    · rw [←heap.ownership layout]
      exact f.ownership related storage owned oldPresent

#print axioms replace_checked
end Binary.Pair.Replace
