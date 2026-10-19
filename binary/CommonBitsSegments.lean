import CommonBitsRegions
import CommonBitsLayout
import AllowedipsLoopRegion

namespace Binary.CommonBits
local instance : Labels := Image.linkedLabels

/-- Prefixes retain the exact fetched layout; no new decoding premise. -/
theorem layout_take {fetch pc code} (layout : LaidOut fetch pc code) (n : Nat) :
    LaidOut fetch pc (code.take n) := by
  induction layout generalizing n with
  | nil => simp only [List.take_nil]; exact .nil _
  | cons pc i len tail positive here mono rest ih =>
    cases n with
    | zero => exact .nil _
    | succ n => exact .cons pc i len _ positive here mono (ih n)

private theorem low_extend32 (v : BitVec 32) : (v.setWidth 64).extractLsb' 0 32 = v := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

private theorem low_xor64 (a b : BitVec 64) :
    (a ^^^ b).extractLsb' 0 32 = a.extractLsb' 0 32 ^^^ b.extractLsb' 0 32 := by
  exact BitVec.extractLsb'_xor

theorem family32_arguments_prefix (s : MachineData) :
    (run (AllowedipsImage.CommonBits.r15.take 2) 0x15 s).All (fun t =>
      t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x1c) := by
  simp [run, AllowedipsImage.CommonBits.r15, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     ConstExpr.interp,  MachineData.set,
    MachineData.setReg, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.take, BitVec.drop, Effects.All,
    List.take,   AllowedipsImage.CommonBits.entry]

theorem family128_arguments_prefix (s : MachineData) :
    (run (AllowedipsImage.CommonBits.r2b.take 3) 0x2b s).All (fun t =>
      t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 0xffffff80, rbp := 0} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x34) := by
  simp [run, AllowedipsImage.CommonBits.r2b, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     ConstExpr.interp,  MachineData.set,
    MachineData.setReg, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.take, BitVec.drop, Effects.All,
    List.take,   AllowedipsImage.CommonBits.entry]

theorem ipv6_result_seed_prefix (s : MachineData) :
    (run (AllowedipsImage.CommonBits.raf.take 1) 0xaf s).All (fun t =>
      t.data.regs = {s.regs with rbp := 0xffffff80} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0xb4) := by
  simp [run, AllowedipsImage.CommonBits.raf, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp,  Operand.interp,
     ConstExpr.interp,  MachineData.set,
    MachineData.setReg,
    Reg64s.set, Reg64s.set64,   Effects.All,
    List.take,   AllowedipsImage.CommonBits.entry]

theorem high_arguments_prefix (s : MachineData) (stored query : UInt64)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 32) 8 = some stored.toNat)
    (queryField : s.dmem.loadInt s.regs.r13.toBitVec 8 = some query.toNat) :
    (run (AllowedipsImage.CommonBits.r7a.take 4) 0x7a s).All (fun t =>
      t.data.regs = {s.regs with
        rbx := stored, rbp := query, rdi := stored, rsi := query} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x89) := by
  simp [run, AllowedipsImage.CommonBits.r7a, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     ConstExpr.interp,  MachineData.load,
    AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    MachineData.set, MachineData.setReg, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.take, BitVec.drop, Effects.All,
    List.take,   queryField,  AllowedipsImage.CommonBits.entry]
  simp_all [Effects.All]

theorem ipv4_scan_prefix (s : MachineData) (stored query : UInt32)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 32) 4 = some stored.toNat)
    (queryField : s.dmem.loadInt s.regs.r13.toBitVec 4 = some query.toNat) :
    (run (AllowedipsImage.CommonBits.r51.take 6) 0x51 s).All (fun t =>
      let x := stored.toBitVec ^^^ query.toBitVec
      let n := scan32 x + 1
      t.data.regs = {s.regs with
        rdx := .ofBitVec (x.setWidth 64), rax := .ofBitVec (n.setWidth 64),
        rbp := .ofBitVec (((s.regs.get (.low .rbp .W32)) - n).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0x67) := by
  have width8 : (Width.W32 == Width.W8) = false := rfl
  have width32 : (Width.W32 == Width.W32) = true := rfl
  have target : label "L_ffffffff810f3100" = (-2129710848 : Int64) := by decide
  simp [run, AllowedipsImage.CommonBits.r51, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     ConstExpr.interp,  MachineData.load,
    AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    MachineData.set, MachineData.setReg, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.take, BitVec.drop, Effects.All,
    List.take,  width8, width32,  queryField,
      AllowedipsImage.CommonBits.entry]
  simp_all [Effects.All, low_extend32, low_xor64]
  split <;> simp_all [Effects.All, scan32,   BitVec.add_comm]
  · rename_i same
    have eq := UInt32.toBitVec_inj.mp same
    simp [eq]
  · have small : stored.toNat < 4294967296 := stored.toNat_lt_size
    have wide : stored.toNat < 18446744073709551616 := by omega
    have xorSmall : stored.toNat ^^^ query.toNat < 4294967296 :=
      Nat.xor_lt_two_pow (n := 32) stored.toNat_lt_size query.toNat_lt_size
    have castMod : ((stored.toNat : Int) % 4294967296).toNat = stored.toNat := by
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      simp
    simp [castMod, Nat.mod_eq_of_lt small, Nat.mod_eq_of_lt wide,
      Nat.mod_eq_of_lt xorSmall]

theorem epilogue_prefix (offset : Nat) (s : MachineData) (bx bp r12 r13 : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat) :
    (run (AllowedipsImage.CommonBits.r43.take 5) offset s).All (fun t =>
      t.data.regs = {s.regs with
        rax := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+.ofNat (offset+8)) := by
  simp [List.take, run, AllowedipsImage.CommonBits.r43, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
     h0,  ]
  simp_all [Effects.All,  ]
  constructor
  · rfl
  · simp only [Int64.add_assoc]
    rfl

theorem ipv6_epilogue_prefix (s : MachineData) (bx bp r12 r13 : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat) :
    (run (AllowedipsImage.CommonBits.rb9.take 6) 0xb9 s).All (fun t =>
      t.data.regs = {s.regs with
        rax := .ofBitVec (((s.regs.get (.low .rbp .W32)) -
          (s.regs.get (.low .rbx .W32))).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 32} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry+0xc3) := by
  simp [List.take, run, AllowedipsImage.CommonBits.rb9, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
     h0,  ]
  simp_all [Effects.All,  ]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp
  exact ⟨rfl, rfl⟩

end Binary.CommonBits
