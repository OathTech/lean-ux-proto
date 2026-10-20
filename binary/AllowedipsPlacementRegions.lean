import AllowedipsMutationCodeLayout
import CommonBitsSequentialCall
import AllowedipsRegions

namespace Binary.Pair.Allowedips.Placement
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def physical (code : List (Kraken.Sized Directive)) (offset : Nat) (s : MachineData) : Effects :=
  Directives.interp code s (Add.entry+.ofNat offset) (fun pc data => .done ⟨data,pc⟩)

private theorem compare_eq (a b : BitVec 8) : (a-b==0#8)=(a==b) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

theorem cidr_guard (s : MachineData) :
    (physical Add.r10a 0x10a s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=if (s.regs.get (.low .rbp .W8)).toNat ≤ (s.regs.get (.low .r12 .W8)).toNat
        then Add.entry+0x8e else Add.entry+0x113) := by
  simp [physical,Add.r10a,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,Effects.All,StatusFlags.from_result,CondCode.interp,Allowedips.carry8]
  split <;> simp_all [Effects.All,Add.entry]
  all_goals rfl

theorem prefix_guard (s : MachineData) :
    (physical Add.rad 0xad s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=if (s.regs.get (.low .r14 .W8)).toNat < (s.regs.get (.low .rbp .W8)).toNat
        then Add.entry+0x113 else Add.entry+0xb2) := by
  simp [physical,Add.rad,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,Effects.All,StatusFlags.from_result,CondCode.interp,Allowedips.carry8]
  split <;> simp_all [Effects.All,Add.entry]
  all_goals rfl

theorem exact_guard (s : MachineData) :
    (physical Add.rc1 0xc1 s).All (fun t =>
      t.data.regs=s.regs ∧ t.data.dmem=s.dmem ∧
      t.pc=if s.regs.get (.low .r12 .W8)==s.regs.get (.low .rbp .W8)
        then Add.entry+0x3ca else Add.entry+0xca) := by
  simp [physical,Add.rc1,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,Effects.All,StatusFlags.from_result,CondCode.interp,compare_eq]
  split <;> simp_all [Effects.All,Add.entry]
  all_goals rfl

/-- Nonmatching-node exit restores the saved width, peer and last matching parent. -/
theorem restore (s : MachineData) (bits : BitVec 32) (peer parent : BitVec 64)
    (width : s.dmem.loadInt (s.regs.rsp.toBitVec+0x24) 4=some bits.toNat)
    (owner : s.dmem.loadInt (s.regs.rsp.toBitVec+0x18) 8=some peer.toNat)
    (previous : s.dmem.loadInt s.regs.rsp.toBitVec 8=some parent.toNat) :
    (physical Add.r113 0x113 s).All (fun t =>
      t.pc=Add.entry+0x120 ∧ t.data.regs={s.regs with
        rbp := .ofBitVec (bits.setWidth 64),r14 := .ofBitVec peer,rbx := .ofBitVec parent} ∧
      t.data.dmem=s.dmem) := by
  simp [physical,Add.r113,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,Reg64s.get64,Reg64s.set,Reg64s.set64,
    BitVec.take,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All] at width owner previous ⊢
  simp [width,owner,previous,Effects.All,Add.entry]

/-- Argument preparation for common_bits; the CALL itself is shared by both
insertion call sites through CommonBits.Sequential.call_run. -/
theorem common_arguments (s : MachineData) :
    (physical (Add.r93.take 3) 0x93 s).All (fun t =>
      t.pc=Add.entry+0x9c ∧ t.data.regs={s.regs with
        rsi := s.regs.r13,rdi := s.regs.rbx,
        rdx := .ofBitVec ((s.regs.get (.low .r15 .W32)).setWidth 64)} ∧
      t.data.dmem=s.dmem) := by
  simp [physical,Add.r93,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.set,MachineData.setReg,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,Add.entry]

#print axioms cidr_guard
#print axioms prefix_guard
#print axioms exact_guard
#print axioms restore
#print axioms common_arguments
end Binary.Pair.Allowedips.Placement
