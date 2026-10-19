import AllowedipsMoves
import TrustBase

namespace Binary.Allowedips
local instance : Labels := Image.linkedLabels

/-- Only the preempt word and byte-sized bit-length copy change here. -/
theorem disableBottomHalves (s : MachineData) (old : BitVec 32)
    (field : s.dmem.loadInt TrustBase.preemptCountAddress 4 = some old.toNat) :
    (run AllowedipsImage.Lookup.r66 0x66 s).All (fun t =>
      t.data.regs = {s.regs with r13 := .ofBitVec ((s.regs.get (.low .r12 .W8)).setWidth 64)} ∧
      t.data.dmem = s.dmem.storeInt TrustBase.preemptCountAddress 4 (old+512).toInt ∧
      t.pc = AllowedipsImage.Lookup.entry+0x74) := by
  simp [run, AllowedipsImage.Lookup.r66, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
     BitVec.signed,
     Effects.All, AllowedipsImage.Lookup.entry,
    TrustBase.preemptCountAddress] at field ⊢
  rw [field]
  simp [Effects.All, ]
  simp [BitVec.toInt_eq_toNat_bmod, Int.add_comm]

/-- The helper result is saved across instrumentation and BH-enable. -/
theorem saveResult (s : MachineData) (old : Int)
    (mapped : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some old) :
    (run (AllowedipsImage.Lookup.r122.take 1) 0x122 s).All (fun t =>
      t.data.regs = s.regs ∧
      t.data.dmem = s.dmem.storeInt s.regs.rsp.toBitVec 8 s.regs.rax.toBitVec.toInt ∧
      t.pc = AllowedipsImage.Lookup.entry+0x126) := by
  simp [run, AllowedipsImage.Lookup.r122, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, AddrExpr.interp, ConstExpr.interp,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt,
    Effects.All, AllowedipsImage.Lookup.entry, mapped]

/-- The ABI return reads the saved result and restores all six callee-saved
    registers and the original return address. -/
theorem epilogue (s : MachineData) (result bx bp r12 r13 r14 r15 ra : UInt64)
    (value : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some result.toNat)
    (h0 : s.dmem.loadInt (s.regs.rsp.toBitVec+32) 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+40) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+48) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+56) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+64) 8 = some r14.toNat)
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+72) 8 = some r15.toNat)
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+80) 8 = some ra.toNat) :
    (run AllowedipsImage.Lookup.r13c 0x13c s).All (fun t =>
      t.data.regs = {s.regs with
        rax := result, rbx := bx, rbp := bp, r12, r13, r14, r15, rsp := s.regs.rsp+88} ∧
      t.data.dmem = s.dmem ∧ t.pc = .ofBitVec ra.toBitVec) := by
  have add32 (x : BitVec 64) : 32+x=x+32 := BitVec.add_comm _ _
  have add32u (x : UInt64) : 32+x=x+32 := UInt64.add_comm _ _
  simp [run, AllowedipsImage.Lookup.r13c, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg, AddrExpr.interp,
    ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt,
     Effects.All, AllowedipsImage.Lookup.entry,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
      add32u, value,      ]
  simp_all [Effects.All,  ]
  apply Int64.toBitVec_inj.mp
  simp

#print axioms disableBottomHalves
#print axioms saveResult
#print axioms epilogue
end Binary.Allowedips
