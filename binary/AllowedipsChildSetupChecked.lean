import AllowedipsChildSetupRegions
import AllowedipsStackReady

namespace Binary.Pair.Allowedips.ChildSetup
open AllowedipsMutationImage Root
local instance : Labels := Image.linkedLabels

def Writes (stack : UInt64) : BitVec 64 → Prop := InRange stack.toBitVec 32

theorem store_window {stack : UInt64} {offset size value : Nat} {before after : DataMem}
    (within : offset+size≤32) (checked : store before (stack.toNat+offset) size value=.ok after) :
    EqualOutside (Writes stack) before after ∧ MappedLe before after := by
  have actual := (store_facts checked).2
  rw [actual]
  refine ⟨?_,MappedLe.store _ _ _ _⟩
  intro a outside
  apply storeInt_frame _ _ _ _ a
  rintro ⟨i,bound,equal⟩
  apply outside
  refine ⟨offset+i,by omega,?_⟩
  simpa only [BitVec.ofNat_add,ofNat_uint64,BitVec.add_assoc] using equal

theorem entry_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s : MachineData} {memory : DataMem} {offset : Nat}
    (checked : entryEffect s=.ok (memory,offset)) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+.ofNat offset ∧ t.data.regs=s.regs ∧ t.data.dmem=memory ∧
      EqualOutside (Writes s.regs.rsp) s.dmem t.data.dmem ∧ MappedLe s.dmem t.data.dmem)
      ⟨s,Add.entry+0x1ff⟩ := by
  unfold entryEffect at checked
  obtain ⟨_,stored,checked⟩ := bind_ok checked
  cases Except.ok.inj checked
  have frame := store_window (by decide : 24+8≤32) stored
  obtain ⟨mapped,actual⟩ := store_facts stored
  rw [store_nat64] at actual
  have actual : memory=s.dmem.storeInt (s.regs.rsp.toBitVec+24) 8 s.regs.r8.toBitVec.toInt := by
    simpa [BitVec.ofNat_add,ofNat_uint64] using actual
  have physical := entry_step s (by simpa [BitVec.ofNat_add,ofNat_uint64] using mapped)
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (Add_r1ff_layout.agreement decoder.add) s _ physical)
  rintro t ⟨pc,regs,mem⟩
  have memEq : t.data.dmem=memory := mem.trans actual.symm
  refine ⟨?_,regs,memEq,memEq ▸ frame.1,memEq ▸ frame.2⟩
  rw [pc]
  split <;> rfl

theorem save_checked (fetch : Int64 → Option Decoded)
    (decoder : TrustBase.AllowedipsMutationDecoderAgreement fetch)
    {s : MachineData} {memory : DataMem} (checked : saveEffect s=.ok memory) :
    Eventually (instructionStep fetch) (fun t =>
      t.pc=Add.entry+0x6ed ∧ t.data.regs=s.regs ∧ t.data.dmem=memory ∧
      EqualOutside (Writes s.regs.rsp) s.dmem t.data.dmem ∧ MappedLe s.dmem t.data.dmem)
      ⟨s,Add.entry+0x6e0⟩ := by
  unfold saveEffect at checked
  obtain ⟨first,stored0,checked⟩ := bind_ok checked
  obtain ⟨second,stored1,stored2⟩ := bind_ok checked
  have firstFrame := store_window (by decide : 16+8≤32) stored0
  have secondFrame := store_window (by decide : 8+1≤32) stored1
  have lastFrame := store_window (stack:=s.regs.rsp) (offset:=0) (by decide : 0+8≤32)
    (by simpa only [Nat.add_zero] using stored2)
  obtain ⟨mapped0,actual0⟩ := store_facts stored0
  obtain ⟨mapped1,actual1⟩ := store_facts stored1
  obtain ⟨mapped2,actual2⟩ := store_facts stored2
  rw [store_nat64] at actual0 actual2
  have byteEq : BitVec.ofNat 8 (s.regs.rdx.toNat%256)=s.regs.get (.low .rdx .W8) := by
    apply BitVec.eq_of_toNat_eq
    simp [Reg64s.get,Reg64s.get64,Reg.base,Reg.offset,BitVec.take,BitVec.drop]
  rw [store_nat,byteEq] at actual1
  have actual2 : memory=second.storeInt s.regs.rsp.toBitVec 8 s.regs.r8.toBitVec.toInt := by
    simpa only [ofNat_uint64] using actual2
  have physical := save_step s first second
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using mapped0)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using actual0)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using mapped1)
    (by simpa [BitVec.ofNat_add,ofNat_uint64] using actual1)
    (by simpa only [ofNat_uint64] using mapped2)
  have layout : LaidOut Add.fetch (Add.entry+0x6e0) (Add.r6e0.take 3) := by binary_layout
  apply eventually_weaken (instructionStep fetch) _ _ _ _
    (region_eventually (layout.agreement decoder.add) s _ physical)
  rintro t ⟨pc,regs,mem⟩
  have memEq : t.data.dmem=memory := mem.trans actual2.symm
  refine ⟨pc,regs,memEq,?_,memEq ▸ firstFrame.2.trans (secondFrame.2.trans lastFrame.2)⟩
  rw [memEq]
  intro a outside
  exact (firstFrame.1 a outside).trans ((secondFrame.1 a outside).trans (lastFrame.1 a outside))

#print axioms entry_checked
#print axioms save_checked
end Binary.Pair.Allowedips.ChildSetup
