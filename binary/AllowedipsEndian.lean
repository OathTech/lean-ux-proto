import AllowedipsMoves
import AllowedipsWords
import MemoryBytes
import StackFrame

namespace Binary.Allowedips
local instance : Labels := Image.linkedLabels

/-- The input is loaded in network order; the stack receives the host-order
    word through the binary's actual BSWAP, not a substituted conversion. -/
theorem endian32 (s : MachineData) (network : BitVec 32) (old : Int)
    (input : s.dmem.loadInt s.regs.rbp.toBitVec 4 = some network.toNat)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 4 = some old) :
    (run AllowedipsImage.Lookup.r176 0x176 s).All (fun t =>
      t.data.regs = {s.regs with rax := .ofBitVec ((swap32 network).setWidth 64)} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec+16) 4 (swap32 network).toInt ∧
      t.pc = AllowedipsImage.Lookup.entry+0x61) := by
  have target : label "L_ffffffff813a0a91" = AllowedipsImage.Lookup.entry+0x61 := by decide
  simp [run, AllowedipsImage.Lookup.r176, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt, BitVec.ofInt_add,
    BitVec.ofInt_ofNat, Effects.All, AllowedipsImage.Lookup.entry, target] at input mapped ⊢
  rw [input]
  simp only [Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp only [mapped,   Effects.All]
  simp only [swap32, ]
  simp only [BitVec.extractLsb'_setWidth_of_le (by decide : 8+8 ≤ 64),
    BitVec.extractLsb'_setWidth_of_le (by decide : 16+8 ≤ 64),
    BitVec.extractLsb'_setWidth_of_le (by decide : 24+8 ≤ 64)]
  simp only [BitVec.setWidth_eq, and_true, true_and]
  change s.dmem.storeInt _ 4 (((swap32 network).toNat : Int) % 18446744073709551616 |>.bmod 4294967296) =
    s.dmem.storeInt _ 4 (swap32 network).toInt
  have bound := (swap32 network).isLt
  rw [Int.emod_eq_of_lt (by omega) (by omega)]
  rw [BitVec.toInt_eq_toNat_bmod]

#print axioms endian32

def highStored (s : MachineData) (network : BitVec 64) : Mem 64 :=
  s.dmem.storeInt (s.regs.rsp.toBitVec+16) 8 (swap64 network).toInt

/-- Exact two-word conversion. The low read is stated in the memory after
    the first store; the invocation proof derives it by its input frame. -/
theorem endian128 (s : MachineData) (high low : BitVec 64) (oldHigh oldLow : Int)
    (inputHigh : s.dmem.loadInt s.regs.rbp.toBitVec 8 = some high.toNat)
    (mappedHigh : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 8 = some oldHigh)
    (inputLow : (highStored s high).loadInt (s.regs.rbp.toBitVec+8) 8 = some low.toNat)
    (mappedLow : (highStored s high).loadInt (s.regs.rsp.toBitVec+24) 8 = some oldLow) :
    (run AllowedipsImage.Lookup.r154 0x154 s).All (fun t =>
      t.data.regs = {s.regs with rax := .ofBitVec (swap64 low)} ∧
      t.data.dmem = (highStored s high).storeInt (s.regs.rsp.toBitVec+24) 8 (swap64 low).toInt ∧
      t.pc = AllowedipsImage.Lookup.entry+0x61) := by
  have target : label "L_ffffffff813a0a91" = AllowedipsImage.Lookup.entry+0x61 := by decide
  simp [run, AllowedipsImage.Lookup.r154, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt, BitVec.ofInt_add,
    BitVec.ofInt_ofNat, Effects.All, AllowedipsImage.Lookup.entry, target] at inputHigh mappedHigh ⊢
  rw [inputHigh]
  simp only [Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_eq,  mappedHigh, ]
  change Effects.All _ (match (highStored s high).loadInt (s.regs.rbp.toBitVec+8) 8 with
    | some i => _
    | none => _)
  rw [inputLow]
  simp [Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
     swap64, ]
  change Effects.All _ (match (highStored s high).loadInt (s.regs.rsp.toBitVec+24) 8 with
    | some _ => _
    | none => _)
  rw [mappedLow]
  simp [Effects.All, highStored, swap64, ]

#print axioms endian128
end Binary.Allowedips
