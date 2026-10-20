import AllowedipsPlacementCommon

namespace Binary.Pair.Allowedips.Placement
open TrustBase CommonBitsCoverage AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

theorem child_guard (s : MachineData) :
    (physical Add.ree 0xee s).All (fun t =>
      t.data=s ∧ t.pc=if s.status.zf then Add.entry+0x55f else Add.entry+0xf4) := by
  simp [physical,Add.ree,Directives.interp,Directive.interp,Instr.interp,Operation.interp,CondCode.interp]
  by_cases h : s.status.zf=true <;> simp [h,Effects.All,Add.entry] <;> rfl

theorem child_move (s : MachineData) :
    (physical Add.rf4 0xf4 s).All (fun t => t.pc=Add.entry+0xf7 ∧
      t.data.regs={s.regs with rbx := s.regs.rax} ∧ t.data.dmem=s.dmem) := by
  simp [physical,Add.rf4,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.set,MachineData.setReg,Reg64s.get,Reg64s.get64,
    Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,BitVec.take,BitVec.drop,Effects.All,Add.entry]

theorem empty_restore (s : MachineData) (bits : BitVec 32) (peer : BitVec 64)
    (width : s.dmem.loadInt (s.regs.rsp.toBitVec+0x24) 4=some bits.toNat)
    (owner : s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some peer.toNat) :
    (physical Add.r55f 0x55f s).All (fun t =>
      t.pc=Add.entry+0x120 ∧ t.data.regs={s.regs with
        rbp := .ofBitVec (bits.setWidth 64),r14 := .ofBitVec peer} ∧ t.data.dmem=s.dmem) := by
  simp [physical,Add.r55f,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,RelRegOrMem.interp,ConstExpr.interp,Reg64s.get64,Reg64s.set,Reg64s.set64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,BitVec.ofInt_toInt,BitVec.ofInt_add,
    BitVec.ofInt_ofNat,Effects.All] at width owner ⊢
  simp [width,owner,Effects.All,Add.entry]
  rfl

theorem Frame.branch {fetch pc code} (layout : LaidOut fetch pc code)
    {base c s} (frame : Frame base c s) (next : Int64)
    (executed : (Directives.interp code s pc (fun pc data => .done ⟨data,pc⟩)).All
      (fun t => t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧ t.pc=next)) :
    Eventually (instructionStep fetch) (fun t => t.pc=next ∧ Frame base c t.data ∧
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem) ⟨s,pc⟩ := by
  apply eventually_weaken (instructionStep fetch) _ _ _ _ (region_eventually layout s _ executed)
  rintro t ⟨regs,memory,pc⟩
  exact ⟨pc,frame.congr memory (by rw [regs]) (by rw [regs]) (by rw [regs]) (by rw [regs]),regs,memory⟩

theorem Frame.restore (fetch : Int64 → Option Decoded) (decoder : AllowedipsMutationDecoderAgreement fetch)
    {base c s} (frame : Frame base c s) (bits : BitVec 32) (peer parent : BitVec 64)
    (width : s.dmem.loadInt (s.regs.rsp.toBitVec+0x24) 4=some bits.toNat)
    (owner : s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some peer.toNat)
    (previous : s.dmem.loadInt s.regs.rsp.toBitVec 8=some parent.toNat) :
    Eventually (instructionStep fetch) (fun t => t.pc=Add.entry+0x120 ∧ Frame base c t.data ∧
      t.data.regs.rbp=.ofBitVec (bits.setWidth 64) ∧ t.data.regs.r14=.ofBitVec peer ∧
      t.data.regs.rbx=.ofBitVec parent) ⟨s,Add.entry+0x113⟩ := by
  have run := region_eventually (Add_r113_layout.agreement decoder.add) s _ (Placement.restore s bits peer parent width owner previous)
  apply eventually_weaken (instructionStep fetch) _ _ _ _ run
  rintro t ⟨pc,regs,memory⟩
  exact ⟨pc,frame.congr memory (by rw [regs]) (by rw [regs]) (by rw [regs]) (by rw [regs]),
    by simp [regs],by simp [regs],by simp [regs]⟩

#print axioms Frame.restore
#print axioms child_move
#print axioms empty_restore
end Binary.Pair.Allowedips.Placement
