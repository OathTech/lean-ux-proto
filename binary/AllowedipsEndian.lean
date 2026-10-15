import AllowedipsMoves
import MemoryBytes
import StackFrame

namespace Binary.Allowedips
local instance : Labels := Image.linkedLabels
set_option linter.unusedSimpArgs false

def swap32 (a : BitVec 32) : BitVec 32 :=
  a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.drop 24

def swap64 (a : BitVec 64) : BitVec 64 :=
  a.take 8 ++ a.extractLsb' 8 8 ++ a.extractLsb' 16 8 ++ a.extractLsb' 24 8 ++
    a.extractLsb' 32 8 ++ a.extractLsb' 40 8 ++ a.extractLsb' 48 8 ++ a.drop 56

/-- The input is loaded in network order; the stack receives the host-order
    word through the binary's actual BSWAP, not a substituted conversion. -/
theorem endian32 (s : MachineData) (network : BitVec 32) (old : Int)
    (input : s.dmem.loadInt s.regs.rbp.toBitVec 4 = some network.toNat)
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec+16) 4 = some old) :
    (run AllowedipsImage.Lookup.r176 0x176 s).All (fun t =>
      t.data.regs = {s.regs with rax := .ofBitVec ((swap32 network).setWidth 64)} ∧
      t.data.dmem = s.dmem.storeInt (s.regs.rsp.toBitVec+16) 4 (swap32 network).toInt ∧
      t.pc = AllowedipsImage.Lookup.entry+0x61) := by
  have target : label "L_ffffffff813a0891" = AllowedipsImage.Lookup.entry+0x61 := by decide
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
  simp only [mapped, Option.isSome_some, ↓reduceIte, Effects.All]
  simp only [swap32, BitVec.take, BitVec.drop]
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
end Binary.Allowedips
