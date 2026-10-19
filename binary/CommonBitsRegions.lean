import AllowedipsImage
import Memory
import Kraken.X64.OmniSemantics

namespace Binary.CommonBits
local instance : Labels := Image.linkedLabels

def run (code : List (Kraken.Sized Directive)) (offset : Nat) (s : MachineData) : Effects :=
  Directives.interp code s (AllowedipsImage.CommonBits.entry + .ofNat offset)
    (fun p d => .done ⟨d, p⟩)

private theorem compare_eq {w : Nat} (a b : BitVec w) :
    (a - b == 0#w) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

/-- The first family decision reads BL, not all of the incoming EDX. -/
theorem family32 (s : MachineData) :
    (run AllowedipsImage.CommonBits.r21 0x21 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbx .W8) == 32 then
        AllowedipsImage.CommonBits.entry + 0x4c else AllowedipsImage.CommonBits.entry + 0x26) := by
  simp [run, AllowedipsImage.CommonBits.r21, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,  ConstExpr.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp, compare_eq]
  split <;> simp_all [Effects.All, AllowedipsImage.CommonBits.entry] <;> rfl

/-- The second family decision also reads only the byte-sized C argument. -/
theorem family128 (s : MachineData) :
    (run AllowedipsImage.CommonBits.r39 0x39 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbx .W8) == 128 then
        AllowedipsImage.CommonBits.entry + 0x75 else AllowedipsImage.CommonBits.entry + 0x3e) := by
  simp [run, AllowedipsImage.CommonBits.r39, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,  ConstExpr.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp, compare_eq]
  split <;> simp_all [Effects.All, AllowedipsImage.CommonBits.entry] <;> rfl

/-- Comparing the high words selects whether the low words are read at all. -/
theorem high_equal (s : MachineData) :
    (run AllowedipsImage.CommonBits.r8e 0x8e s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbx .W64) == s.regs.get (.low .rbp .W64) then
        AllowedipsImage.CommonBits.entry + 0xc4 else AllowedipsImage.CommonBits.entry + 0x93) := by
  simp [run, AllowedipsImage.CommonBits.r8e, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp, compare_eq]
  split <;> simp_all [Effects.All, AllowedipsImage.CommonBits.entry] <;> rfl

/-- The seeded 64-bit BSR result, before the subsequent 32-bit addition. -/
def scan64 (x : BitVec 64) : BitVec 64 :=
  if x = 0 then 0xffffffff else .ofNat 64 x.toNat.log2

/-- Exact high-word arithmetic, with all undefined flag choices quantified. -/
theorem high_scan (s : MachineData) :
    (run AllowedipsImage.CommonBits.r98 0x98 s).All (fun t =>
      let x := s.regs.rbx.toBitVec ^^^ s.regs.rbp.toBitVec
      t.data.regs = {s.regs with
        rax := .ofBitVec x, rbx := .ofBitVec (((scan64 x).setWidth 32 + 65).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry + 0xaa) := by
  have width8 : (Width.W64 == Width.W8) = false := rfl
  have width32 : (Width.W64 == Width.W32) = false := rfl
  simp [run, AllowedipsImage.CommonBits.r98, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,  ConstExpr.interp,
    MachineData.set, MachineData.setReg, Reg64s.get, Reg64s.get64,
    Reg64s.set, Reg64s.set64, Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    Effects.All, width8, width32, AllowedipsImage.CommonBits.entry]
  split <;> simp_all [Effects.All, scan64]
  rw [← BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [BitVec.add_comm]


/-- Only the equal-high-word path reads these two low words. -/
theorem low_scan (s : MachineData) (stored query : BitVec 64)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 40) 8 = some stored.toNat)
    (queryField : s.dmem.loadInt (s.regs.r13.toBitVec + 8) 8 = some query.toNat) :
    (run AllowedipsImage.CommonBits.rc9 0xc9 s).All (fun t =>
      let x := stored ^^^ query
      t.data.regs = {s.regs with
        rax := .ofBitVec x, rbx := .ofBitVec (((scan64 x).setWidth 32 + 1).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.CommonBits.entry + 0xaa) := by
  have target : label "L_ffffffff813a07fa" = (-2126903302 : Int64) := by decide
  have width8 : (Width.W64 == Width.W8) = false := rfl
  have width32 : (Width.W64 == Width.W32) = false := rfl
  simp [run, AllowedipsImage.CommonBits.rc9, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp, RelRegOrMem.interp, ConstExpr.interp,
    MachineData.load, AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    MachineData.set, MachineData.setReg, Reg64s.get, Reg64s.get64,
    Reg64s.set, Reg64s.set64, Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    Effects.All, width8, width32, target, AllowedipsImage.CommonBits.entry,
    storedField, queryField] at storedField queryField ⊢
  simp_all only [   ]
  split <;> simp_all [Effects.All, scan64]
  rw [← BitVec.setWidth_eq_extractLsb' (by decide)]
  simp [BitVec.add_comm]

def callMemory (s : MachineData) (returnOffset : Nat) : DataMem :=
  s.dmem.storeInt (s.regs.rsp.toBitVec - 8) 8
    (AllowedipsImage.CommonBits.entry + .ofNat returnOffset).toBitVec.toInt

/-- Each singleton PC callback region executes the real CALL and stores its return address. -/
theorem trace_call (offset : Nat) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run AllowedipsImage.CommonBits.r26 offset s).All (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (offset + 5) ∧ t.pc = .ofNat 0xffffffff810f3100) := by
  simp [run, AllowedipsImage.CommonBits.r26, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, MachineData.store,
    Reg64s.get64, Reg64s.set64, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory]
  simp_all [Effects.All,  Int64.add_assoc]
  constructor
  · simp [Int.add_assoc]
  · have cancel (a b : Int64) : a + (b - a) = b := by
      apply Int64.toBitVec_inj.mp
      simp only [Int64.toBitVec_add, Int64.toBitVec_sub]
      rw [BitVec.add_comm]
      exact BitVec.sub_add_cancel _ _
    simpa only [Int64.add_assoc] using
      (cancel (AllowedipsImage.CommonBits.entry + Int64.ofNat offset + 5)
        (label "L_ffffffff810f3100")).trans (show label "L_ffffffff810f3100" =
          (-2129710848 : Int64) from by decide)

theorem trace_region_terms :
    AllowedipsImage.CommonBits.r3e = AllowedipsImage.CommonBits.r26 ∧
    AllowedipsImage.CommonBits.r4c = AllowedipsImage.CommonBits.r26 ∧
    AllowedipsImage.CommonBits.r75 = AllowedipsImage.CommonBits.r26 ∧
    AllowedipsImage.CommonBits.r93 = AllowedipsImage.CommonBits.r26 ∧
    AllowedipsImage.CommonBits.raa = AllowedipsImage.CommonBits.r26 ∧
    AllowedipsImage.CommonBits.rc4 = AllowedipsImage.CommonBits.r26 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- The first byte comparison callback receives the preserved family argument. -/
theorem family32_arguments (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run AllowedipsImage.CommonBits.r15 0x15 s).All (fun t =>
      t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 32, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x21 ∧ t.pc = .ofNat 0xffffffff810f3ec0) := by
  simp [run, AllowedipsImage.CommonBits.r15, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, ConstExpr.interp, MachineData.store, MachineData.set,
    MachineData.setReg, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.take, BitVec.drop, Effects.All,
    Width.bytesv,  callMemory, AllowedipsImage.CommonBits.entry]
  simp_all [Effects.All]
  rfl

/-- The second callback receives the byte pattern 0x80; EBP is cleared for invalid families. -/
theorem family128_arguments (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run AllowedipsImage.CommonBits.r2b 0x2b s).All (fun t =>
      t.data.regs = {s.regs with
        rsi := .ofBitVec ((s.regs.get (.low .rbx .W32)).setWidth 64),
        rdi := 0xffffff80, rbp := 0, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x39 ∧ t.pc = .ofNat 0xffffffff810f3ec0) := by
  simp [run, AllowedipsImage.CommonBits.r2b, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, ConstExpr.interp, MachineData.store, MachineData.set,
    MachineData.setReg, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.take, BitVec.drop, Effects.All,
    Width.bytesv,  callMemory, AllowedipsImage.CommonBits.entry]
  simp_all [Effects.All]
  rfl

/-- The 128-bit result uses a sign-extended immediate whose low byte is 128. -/
theorem ipv6_result_seed (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run AllowedipsImage.CommonBits.raf 0xaf s).All (fun t =>
      t.data.regs = {s.regs with rbp := 0xffffff80, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0xb9 ∧ t.pc = .ofNat 0xffffffff810f3100) := by
  simp [run, AllowedipsImage.CommonBits.raf, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp,  Operand.interp,
    RelRegOrMem.interp, ConstExpr.interp, MachineData.store, MachineData.set,
    MachineData.setReg,  Reg64s.get64,
    Reg64s.set, Reg64s.set64,   Effects.All,
    Width.bytesv,  callMemory, AllowedipsImage.CommonBits.entry]
  simp_all [Effects.All]
  rfl

/-- The high words are loaded in host order and passed unchanged to trace_cmp8. -/
theorem high_arguments (s : MachineData) (stored query : UInt64) (stackWord : Int)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 32) 8 = some stored.toNat)
    (queryField : s.dmem.loadInt s.regs.r13.toBitVec 8 = some query.toNat)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run AllowedipsImage.CommonBits.r7a 0x7a s).All (fun t =>
      t.data.regs = {s.regs with
        rbx := stored, rbp := query, rdi := stored, rsi := query, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x8e ∧ t.pc = .ofNat 0xffffffff810f3ea0) := by
  simp [run, AllowedipsImage.CommonBits.r7a, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, ConstExpr.interp, MachineData.store, MachineData.load,
    AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    MachineData.set, MachineData.setReg, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.take, BitVec.drop, Effects.All,
    Width.bytesv,   queryField, callMemory, AllowedipsImage.CommonBits.entry]
  simp_all [Effects.All]
  rfl

def scan32 (x : BitVec 32) : BitVec 32 :=
  if x = 0 then 0xffffffff else .ofNat 32 x.toNat.log2

private theorem low_extend32 (v : BitVec 32) : (v.setWidth 64).extractLsb' 0 32 = v := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

private theorem low_xor64 (a b : BitVec 64) :
    (a ^^^ b).extractLsb' 0 32 = a.extractLsb' 0 32 ^^^ b.extractLsb' 0 32 := by
  exact BitVec.extractLsb'_xor

/-- IPv4 arithmetic through the real final callback CALL, including equal keys.
    Both permitted zero-BSR upper-half outcomes coincide because MOV EAX seeded it. -/
theorem ipv4_scan (s : MachineData) (stored query : UInt32) (stackWord : Int)
    (storedField : s.dmem.loadInt (s.regs.r12.toBitVec + 32) 4 = some stored.toNat)
    (queryField : s.dmem.loadInt s.regs.r13.toBitVec 4 = some query.toNat)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run AllowedipsImage.CommonBits.r51 0x51 s).All (fun t =>
      let x := stored.toBitVec ^^^ query.toBitVec
      let n := scan32 x + 1
      t.data.regs = {s.regs with
        rdx := .ofBitVec (x.setWidth 64), rax := .ofBitVec (n.setWidth 64),
        rbp := .ofBitVec (((s.regs.get (.low .rbp .W32)) - n).setWidth 64),
        rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x6c ∧ t.pc = .ofNat 0xffffffff810f3100) := by
  have width8 : (Width.W32 == Width.W8) = false := rfl
  have width32 : (Width.W32 == Width.W32) = true := rfl
  have target : label "L_ffffffff810f3100" = (-2129710848 : Int64) := by decide
  simp [run, AllowedipsImage.CommonBits.r51, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, ConstExpr.interp, MachineData.store, MachineData.load,
    AddrExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    MachineData.set, MachineData.setReg, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.take, BitVec.drop, Effects.All,
    Width.bytesv, width8, width32,   queryField,
    callMemory, target, AllowedipsImage.CommonBits.entry]
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


/-- The common_bits ABI saves four registers. RET consumes the fifth word. -/
theorem epilogue (offset : Nat) (s : MachineData) (bx bp r12 r13 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec + 32) 8 = some ra.toNat) :
    (run AllowedipsImage.CommonBits.r43 offset s).All (fun t =>
      t.data.regs = {s.regs with
        rax := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 40} ∧
      t.data.dmem = s.dmem ∧ t.pc = .ofBitVec ra.toBitVec) := by
  simp [run, AllowedipsImage.CommonBits.r43, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
     h0,   ]
  simp_all [Effects.All,  ]
  apply Int64.toBitVec_inj.mp
  simp

theorem epilogue_region_terms : AllowedipsImage.CommonBits.r6c = AllowedipsImage.CommonBits.r43 := rfl

/-- IPv6 subtracts before restoring RBX, and moves the result before restoring RBP. -/
theorem ipv6_epilogue (s : MachineData) (bx bp r12 r13 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec + 32) 8 = some ra.toNat) :
    (run AllowedipsImage.CommonBits.rb9 0xb9 s).All (fun t =>
      t.data.regs = {s.regs with
        rax := .ofBitVec (((s.regs.get (.low .rbp .W32)) -
          (s.regs.get (.low .rbx .W32))).setWidth 64),
        rbx := bx, rbp := bp, r12, r13, rsp := s.regs.rsp + 40} ∧
      t.data.dmem = s.dmem ∧ t.pc = .ofBitVec ra.toBitVec) := by
  simp [run, AllowedipsImage.CommonBits.rb9, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
     h0,   ]
  simp_all [Effects.All,  ]
  constructor
  · rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
    simp
  · apply Int64.toBitVec_inj.mp
    simp

def savedWords (s : MachineData) : List UInt64 :=
  [s.regs.r13, s.regs.r12, s.regs.rbp, s.regs.rbx,
    (AllowedipsImage.CommonBits.entry + 0x15).toUInt64]

def saveMemory (s : MachineData) : Nat → DataMem
  | 0 => s.dmem
  | n + 1 => (saveMemory s n).storeInt
      (s.regs.rsp.toBitVec - .ofNat 64 ((n + 1) * 8)) 8
      ((savedWords s)[n]?.getD 0).toBitVec.toInt

theorem saves_preserve_mapped (s : MachineData) (n : Nat) (a : BitVec 64)
    (h : (s.dmem.loadInt a 8).isSome = true) :
    ((saveMemory s n).loadInt a 8).isSome = true := by
  induction n with
  | zero => exact h
  | succ n ih => exact storeInt_defined _ _ _ _ _ _ ih

/-- Four interleaved saves and argument copies, then the actual entry callback.
    The only premise is mapping of the five written stack words. -/
theorem prologue (s : MachineData)
    (stack : ∀ n < 5,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n + 1) * 8)) 8).isSome = true) :
    (run AllowedipsImage.CommonBits.r00 0 s).All (fun t =>
      t.data.regs = {s.regs with
        r13 := s.regs.rsi, r12 := s.regs.rdi,
        rbp := .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64),
        rbx := .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64),
        rsp := s.regs.rsp - 40} ∧
      t.data.dmem = saveMemory s 5 ∧ t.pc = .ofNat 0xffffffff810f3100) := by
  have mapped (n : Nat) (hn : n < 5) :=
    saves_preserve_mapped s n _ (stack n hn)
  have h0 := mapped 0 (by decide)
  have h1 := mapped 1 (by decide)
  have h2 := mapped 2 (by decide)
  have h3 := mapped 3 (by decide)
  have h4 := mapped 4 (by decide)
  simp only [Option.isSome_iff_exists] at h0 h1 h2 h3 h4
  obtain ⟨v0, h0⟩ := h0
  obtain ⟨v1, h1⟩ := h1
  obtain ⟨v2, h2⟩ := h2
  obtain ⟨v3, h3⟩ := h3
  obtain ⟨v4, h4⟩ := h4
  simp [run, AllowedipsImage.CommonBits.r00, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  AllowedipsImage.CommonBits.entry,
    saveMemory, savedWords, BitVec.sub_sub] at h0 h1 h2 h3 h4 ⊢
  simp_all [Effects.All]
  rfl


end Binary.CommonBits
