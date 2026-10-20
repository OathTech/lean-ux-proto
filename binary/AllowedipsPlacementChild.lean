import AllowedipsPlacementRegions
import AllowedipsChild

namespace Binary.Pair.Allowedips.Placement
open AllowedipsMutationImage AllowedipsChild
local instance : Labels := Image.linkedLabels

def parentMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt s.regs.rsp.toBitVec 8 s.regs.rbx.toBitVec.toInt

/-- The child edge records the previous node in the caller's stack slot.
The subsequent query/child reads are over that actual written memory. -/
theorem child_step (s : MachineData) (byteIndex shift byte : Nat) (next : BitVec 64)
    (indexBound : byteIndex < 16) (shiftBound : shift < 8) (byteBound : byte < 256)
    (old : Int)
    (mapped : s.dmem.loadInt s.regs.rsp.toBitVec 8=some old)
    (indexRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 25) 1 = some (byteIndex : Int))
    (shiftRead : s.dmem.loadInt (s.regs.rbx.toBitVec + 26) 1 = some (shift : Int))
    (byteRead : (parentMemory s).loadInt (s.regs.r13.toBitVec + .ofNat 64 byteIndex) 1 = some (byte : Int))
    (childRead : (parentMemory s).loadInt (s.regs.rbx.toBitVec + 8 + .ofNat 64 (8 * selected byte shift)) 8 = some next.toNat) :
    (physical Add.rcf 0xcf s).All (fun t => t.pc=Add.entry+0xee ∧
      t.data.dmem=parentMemory s ∧ t.data.regs={s.regs with
        rax := .ofBitVec next,rcx := .ofNat shift} ∧ t.data.status.zf=(next==0)) := by
  simp [parentMemory] at indexRead shiftRead byteRead childRead
  have ix := extend8 byteIndex (by omega)
  have sh := extend8 shift (by omega)
  have by8 := extend8 byte byteBound
  change (BitVec.ofNat 8 byteIndex).setWidth 64 = BitVec.ofNat 64 byteIndex at ix
  change (BitVec.ofNat 8 shift).setWidth 64 = BitVec.ofNat 64 shift at sh
  change (BitVec.ofNat 8 byte).setWidth 64 = BitVec.ofNat 64 byte at by8
  have shiftMask : shift % 256 &&& 31 = shift := by
    rw [Nat.mod_eq_of_lt (by omega), show (31 : Nat) = 2^5-1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  simp [physical,Add.rcf, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
     ConstExpr.interp,  AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_mul, BitVec.ofInt_toInt,
    ix, sh, by8, extract32, low32, BitVec.ofInt_natCast, shiftMask,
    indexRead, shiftRead, byteRead,parentMemory,mapped,
    ShiftCountExpr.interpMasked, ShiftCountExpr.interp,StatusFlags.from_result]
  have childAddr : s.regs.rbx.toBitVec + BitVec.ofNat 64 (selected byte shift) * 8 + 8 =
      s.regs.rbx.toBitVec + 8 + BitVec.ofNat 64 (8 * selected byte shift) := by
    rw [BitVec.ofNat_mul]
    have comm : BitVec.ofNat 64 (selected byte shift) * 8 = 8 * BitVec.ofNat 64 (selected byte shift) := BitVec.mul_comm _ _
    rw [comm]
    ac_rfl
  simp at childAddr
  by_cases zero : shift = 0
  all_goals try simp only [zero] at childRead childAddr
  all_goals simp [-UInt64.ofBitVec_and, Effects.All,   ofInt_bmod64,
      zero]
  all_goals simp only [castmod64, shift_mod byte shift byteBound,  ]
  · have eq0 : byte % 2 = selected byte 0 := by simp [selected]
    simp only [eq0, childAddr, childRead]
    simp [Effects.All, Add.entry]
    subst shift; rfl
  · simp only [childAddr, childRead]
    split <;> simp [Effects.All, Add.entry] <;> rfl


#print axioms child_step
end Binary.Pair.Allowedips.Placement
