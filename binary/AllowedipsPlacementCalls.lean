import AllowedipsPlacementRegions
import PairServiceCall

namespace Binary.Pair.Allowedips.Placement
open AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

def callMemory (s : MachineData) (offset : Nat) : DataMem :=
  s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 (Add.entry+.ofNat offset).toBitVec.toInt

theorem cidr_arguments (s : MachineData) (cidr : BitVec 8) (old : Int)
    (read : s.dmem.loadInt (s.regs.rbx.toBitVec+24) 1=some cidr.toNat)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (physical Add.rfc 0xfc s).All (fun t =>
      t.data.regs={s.regs with
        rbp := .ofBitVec (cidr.setWidth 64),
        rdi := .ofBitVec ((s.regs.get (.low .r12 .W32)).setWidth 64),
        rsi := .ofBitVec (cidr.setWidth 64),rsp := s.regs.rsp-8} ∧
      t.data.dmem=callMemory s 0x10a ∧ t.pc=.ofNat 0xffffffff810f4040) := by
  simp [physical,Add.rfc,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.load,MachineData.store,MachineData.set,MachineData.setReg,
    AddrExpr.interp,ConstExpr.interp,RelRegOrMem.interp,
    Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,BitVec.toAddressSize,BitVec.signed,
    BitVec.ofInt_toInt,BitVec.ofInt_add,BitVec.ofInt_ofNat,Effects.All,Width.bytesv,
    callMemory,Add.entry] at read mapped ⊢
  simp [read,mapped,Effects.All]
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp
    have bound := cidr.isLt
    omega
  · decide

theorem prefix_arguments (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (physical Add.ra1 0xa1 s).All (fun t =>
      let answer := UInt64.ofBitVec ((s.regs.get (.low .rax .W32)).setWidth 64)
      t.data.regs={s.regs with
        rdi := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        r14 := answer,rsi := answer,rsp := s.regs.rsp-8} ∧
      t.data.dmem=callMemory s 0xad ∧ t.pc=.ofNat 0xffffffff810f4040) := by
  simp at mapped
  simp [physical,Add.ra1,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    ConstExpr.interp,RelRegOrMem.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,Width.bytesv,callMemory,Add.entry,mapped]
  decide

theorem exact_arguments (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8=some old) :
    (physical Add.rb7 0xb7 s).All (fun t =>
      t.data.regs={s.regs with
        rdi := .ofBitVec ((s.regs.get (.low .r12 .W32)).setWidth 64),
        rsi := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),rsp := s.regs.rsp-8} ∧
      t.data.dmem=callMemory s 0xc1 ∧ t.pc=.ofNat 0xffffffff810f4040) := by
  simp at mapped
  simp [physical,Add.rb7,Directives.interp,Directive.interp,Instr.interp,Operation.interp,
    RegOrMem.interp,Operand.interp,MachineData.store,MachineData.set,MachineData.setReg,
    ConstExpr.interp,RelRegOrMem.interp,Reg64s.get,Reg64s.get64,Reg64s.set,Reg64s.set64,Reg.base,Reg.offset,
    BitVec.take,BitVec.drop,Effects.All,Width.bytesv,callMemory,Add.entry,mapped]
  decide

#print axioms cidr_arguments
#print axioms prefix_arguments
#print axioms exact_arguments
end Binary.Pair.Allowedips.Placement
