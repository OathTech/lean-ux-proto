import Regions

namespace Binary.PeerGet
local instance : Labels := Image.linkedLabels

private theorem u64_zero (v : UInt64) : v.toBitVec = 0#64 ↔ v = 0 :=
  UInt64.toBitVec_inj

private theorem low32 (v : UInt64) :
    BitVec.ofInt 32 ((v.toNat : Int) % 4294967296) = v.toBitVec.extractLsb' 0 32 := by
  apply BitVec.eq_of_toNat_eq
  simp
  exact Int.toNat_emod (by omega) (by decide)

private theorem truncate_extend (v : BitVec 32) :
    (v.setWidth 64).extractLsb' 0 32 = v := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

private theorem lea_low32 (v : UInt64) :
    (v.toBitVec + 1#64).setWidth 32 = v.toBitVec.extractLsb' 0 32 + 1 := by
  rw [BitVec.setWidth_add _ _ (by decide)]
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  rfl

private theorem mod32_64 (i : Int) :
    (i % 4294967296) % 18446744073709551616 = i % 4294967296 := by
  have h0 := Int.emod_nonneg i (by decide : (4294967296 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos i (by decide : (0 : Int) < 4294967296)
  omega

def run (code : List (Kraken.Sized Directive)) (offset : Nat) (s : MachineData) : Effects :=
  Directives.interp code s (Image.PeerGet.entry + .ofNat offset) (fun p d => .done ⟨d, p⟩)

def callMemory (s : MachineData) (returnOffset : Nat) : DataMem :=
  s.dmem.storeInt (s.regs.rsp.toBitVec - 8) 8
    (Image.PeerGet.entry + .ofNat returnOffset).toBitVec.toInt

/-- All singleton trace-PC regions have this same instruction term. -/
theorem trace_call (offset : Nat) (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.r1b offset s).All (fun t =>
      t.data.regs = {s.regs with rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s (offset + 5) ∧ t.pc = .ofNat 0xffffffff810f3100) := by
  simp [run, Image.PeerGet.r1b, Directives.interp, Directive.interp,
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
      (cancel (Image.PeerGet.entry + Int64.ofNat offset + 5)
        (label "L_ffffffff810f3100")).trans (show label "L_ffffffff810f3100" =
          (-2129710848 : Int64) from by decide)

theorem trace_region_terms :
    Image.PeerGet.r2d = Image.PeerGet.r1b ∧ Image.PeerGet.r3f = Image.PeerGet.r1b ∧
    Image.PeerGet.r69 = Image.PeerGet.r1b ∧ Image.PeerGet.r7b = Image.PeerGet.r1b ∧
    Image.PeerGet.r8f = Image.PeerGet.r1b ∧ Image.PeerGet.r9d = Image.PeerGet.r1b ∧
    Image.PeerGet.rb0 = Image.PeerGet.r1b ∧ Image.PeerGet.rbe = Image.PeerGet.r1b ∧
    Image.PeerGet.rcf = Image.PeerGet.r1b ∧ Image.PeerGet.re1 = Image.PeerGet.r1b := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem refcount_load (s : MachineData) (count : UInt32)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec + 0x420) 4 = some count.toNat) :
    (run Image.PeerGet.r20 0x20 s).All (fun t =>
      t.data.regs = {s.regs with rbp := count.toUInt64, r13 := s.regs.rbx + 0x420} ∧
      t.data.dmem = s.dmem ∧ t.pc = Image.PeerGet.entry + 0x2d) := by
  simp [run, Image.PeerGet.r20, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.interp,  Reg64s.get64,
    Reg64s.set, Reg64s.set64,  BitVec.take,
    ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    Effects.All,  Image.PeerGet.entry]
  simp_all [Effects.All]

def incrementMemory (s : MachineData) : DataMem :=
  s.dmem.storeInt s.regs.r13.toBitVec 4
    (s.regs.get (.low .rbp .W32) + 1).toInt

def incrementRegisters (s : MachineData) : Reg64s :=
  let old := s.regs.get (.low .rbp .W32)
  let regs := s.regs.set (.low .r12 .W32) (old + 1)
  let regs := regs.set (.low .rax .W32) old
  let regs := regs.set (.low .r15 .W8) 1
  let regs := regs.set (.low .rdi .W32) 0
  let regs := regs.set (.low .r14 .W32) old
  let regs := regs.set (.low .rsi .W32) (regs.get (.low .r15 .W32))
  {regs with rsp := s.regs.rsp - 8}

/-- With the single-CPU refcount still equal to the loaded count, CMPXCHG
    succeeds and increments its actual memory word. Upper R15 bits are
    unconstrained: SETE writes only the low byte. -/
theorem increment (s : MachineData) (stackWord : Int)
    (count : s.dmem.loadInt s.regs.r13.toBitVec 4 =
      some (s.regs.get (.low .rbp .W32)).toNat)
    (stack : (incrementMemory s).loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.r44 0x44 s).All (fun t =>
      t.data.regs = incrementRegisters s ∧
      t.data.dmem = (incrementMemory s).storeInt (s.regs.rsp.toBitVec - 8) 8
        (Image.PeerGet.entry + 0x60).toBitVec.toInt ∧
      t.pc = .ofNat 0xffffffff810f3ec0) := by
  simp [run, Image.PeerGet.r44, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.drop, BitVec.take, BitVec.replaceLow,
    RelRegOrMem.interp, ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    Effects.All, CondCode.interp, StatusFlags.from_result, Width.bytesv,
    incrementMemory, incrementRegisters, Image.PeerGet.entry] at count stack ⊢
  simp_all [Effects.All, low32, truncate_extend, lea_low32, mod32_64]
  rfl

theorem null_guard (s : MachineData) :
    (run Image.PeerGet.r12 0x12 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.rbx = 0 then Image.PeerGet.entry + 0xdd else Image.PeerGet.entry + 0x1b) := by
  simp [run, Image.PeerGet.r12, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp]
  by_cases h : s.regs.get (.low .rbx .W64) = 0#64
  all_goals simp_all [Effects.All, Image.PeerGet.entry,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, u64_zero]
  all_goals try rfl

theorem zero_guard (s : MachineData) :
    (run Image.PeerGet.r3b 0x3b s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbp .W32) = 0 then
        Image.PeerGet.entry + 0xb0 else Image.PeerGet.entry + 0x3f) := by
  simp [run, Image.PeerGet.r3b, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp]
  by_cases h : s.regs.get (.low .rbp .W32) = 0#32
  all_goals simp_all [Effects.All, Image.PeerGet.entry]
  rfl

theorem retry_guard (s : MachineData) :
    (run Image.PeerGet.r60 0x60 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .r15 .W8) = 0 then
        Image.PeerGet.entry + 0xf2 else Image.PeerGet.entry + 0x69) := by
  simp [run, Image.PeerGet.r60, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp]
  by_cases h : s.regs.get (.low .r15 .W8) = 0#8
  all_goals simp_all [Effects.All, Image.PeerGet.entry]
  rfl

theorem negative_guard (s : MachineData) :
    (run Image.PeerGet.r77 0x77 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if (s.regs.get (.low .rbp .W32)).msb then
        Image.PeerGet.entry + 0xe1 else Image.PeerGet.entry + 0x7b) := by
  simp [run, Image.PeerGet.r77, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp]
  cases h : (s.regs.get (.low .rbp .W32)).msb <;> simp_all [Effects.All, Image.PeerGet.entry]
  rfl

theorem overflow_guard (s : MachineData) :
    (run Image.PeerGet.r8a 0x8a s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if (s.regs.get (.low .r12 .W32)).msb then
        Image.PeerGet.entry + 0xe1 else Image.PeerGet.entry + 0x8f) := by
  simp [run, Image.PeerGet.r8a, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result, CondCode.interp]
  cases h : (s.regs.get (.low .r12 .W32)).msb <;> simp_all [Effects.All, Image.PeerGet.entry]
  rfl

theorem clear_peer (s : MachineData) :
    (run Image.PeerGet.rdd 0xdd s).All (fun t =>
      t.data.regs = {s.regs with rbx := 0} ∧ t.data.dmem = s.dmem ∧
      t.pc = Image.PeerGet.entry + 0x9d) := by
  simp [run, Image.PeerGet.rdd, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, MachineData.set, MachineData.setReg, Reg64s.set,
    Reg64s.set64, RelRegOrMem.interp, ConstExpr.interp, Image.PeerGet.entry]
  rfl

theorem compare_old (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.r32 0x32 s).All (fun t =>
      t.data.regs = {s.regs with rdi := 0, rsi := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64), rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x3b ∧ t.pc = .ofNat 0xffffffff810f3f00) := by
  simp [run, Image.PeerGet.r32, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory, Image.PeerGet.entry]
  simp_all [Effects.All]
  rfl

#print axioms compare_old

theorem compare_negative (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.r6e 0x6e s).All (fun t =>
      t.data.regs = {s.regs with rdi := 0, rsi := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64), rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x77 ∧ t.pc = .ofNat 0xffffffff810f3f00) := by
  simp [run, Image.PeerGet.r6e, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory, Image.PeerGet.entry]
  simp_all [Effects.All]
  rfl

#print axioms compare_negative

theorem compare_increment (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.r80 0x80 s).All (fun t =>
      t.data.regs = {s.regs with rdi := 0, rsi := .ofBitVec ((s.regs.get (.low .r12 .W32)).setWidth 64), rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x8a ∧ t.pc = .ofNat 0xffffffff810f3f00) := by
  simp [run, Image.PeerGet.r80, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory, Image.PeerGet.entry]
  simp_all [Effects.All]
  rfl

#print axioms compare_increment

theorem compare_result (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.r94 0x94 s).All (fun t =>
      t.data.regs = {s.regs with rdi := 0, rsi := .ofBitVec ((s.regs.get (.low .rbp .W32)).setWidth 64), rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0x9d ∧ t.pc = .ofNat 0xffffffff810f3f00) := by
  simp [run, Image.PeerGet.r94, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory, Image.PeerGet.entry]
  simp_all [Effects.All]
  rfl

#print axioms compare_result

theorem compare_zero (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.rb5 0xb5 s).All (fun t =>
      t.data.regs = {s.regs with rdi := 0, rsi := 0, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0xbe ∧ t.pc = .ofNat 0xffffffff810f3f00) := by
  simp [run, Image.PeerGet.rb5, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory, Image.PeerGet.entry]
  simp_all [Effects.All]
  rfl

#print axioms compare_zero

theorem compare_dead (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.rd4 0xd4 s).All (fun t =>
      t.data.regs = {s.regs with rdi := 0, rsi := 0, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0xdd ∧ t.pc = .ofNat 0xffffffff810f3f00) := by
  simp [run, Image.PeerGet.rd4, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory, Image.PeerGet.entry]
  simp_all [Effects.All]
  rfl

#print axioms compare_dead

theorem compare_one (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.rc3 0xc3 s).All (fun t =>
      t.data.regs = {s.regs with rdi := 0, rsi := 1, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0xcf ∧ t.pc = .ofNat 0xffffffff810f3f00) := by
  simp [run, Image.PeerGet.rc3, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory, Image.PeerGet.entry]
  simp_all [Effects.All]
  rfl

#print axioms compare_one

theorem warn_arguments (s : MachineData) (stackWord : Int)
    (stack : s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8 = some stackWord) :
    (run Image.PeerGet.re6 0xe6 s).All (fun t =>
      t.data.regs = {s.regs with rdi := s.regs.r13, rsi := 0, rsp := s.regs.rsp - 8} ∧
      t.data.dmem = callMemory s 0xf0 ∧ t.pc = .ofNat 0xffffffff812da4d0) := by
  simp [run, Image.PeerGet.re6, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp,
    Effects.All, Width.bytesv,  callMemory, Image.PeerGet.entry]
  simp_all [Effects.All]
  rfl

#print axioms warn_arguments

theorem epilogue (s : MachineData) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some bx.toNat)
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec + 8) 8 = some bp.toNat)
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec + 16) 8 = some r12.toNat)
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec + 24) 8 = some r13.toNat)
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec + 32) 8 = some r14.toNat)
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec + 40) 8 = some r15.toNat)
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec + 48) 8 = some ra.toNat) :
    (run Image.PeerGet.ra2 0xa2 s).All (fun t =>
      t.data.regs = {s.regs with
        rax := s.regs.rbx, rbx := bx, rbp := bp, r12, r13, r14, r15, rsp := s.regs.rsp + 56} ∧
      t.data.dmem = s.dmem ∧ t.pc = .ofBitVec ra.toBitVec) := by
  simp [run, Image.PeerGet.ra2, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
     h0,     ]
  simp_all [Effects.All,  ]
  apply Int64.toBitVec_inj.mp
  simp

#print axioms epilogue

theorem retry_jump (s : MachineData) :
    (run Image.PeerGet.rf2 0xf2 s).All (fun t =>
      t.data.regs = {s.regs with rbp := .ofBitVec ((s.regs.get (.low .r14 .W32)).setWidth 64)} ∧
      t.data.dmem = s.dmem ∧ t.pc = Image.PeerGet.entry + 0x2d) := by
  simp [run, Image.PeerGet.rf2, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, MachineData.set, MachineData.setReg, Reg64s.set,
    Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, RelRegOrMem.interp, ConstExpr.interp, Image.PeerGet.entry]
  rfl

theorem warning_return_jump (s : MachineData) :
    (run Image.PeerGet.rf0 0xf0 s).All (fun t =>
      t.data = s ∧ t.pc = Image.PeerGet.entry + 0x9d) := by
  simp [run, Image.PeerGet.rf0, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, Effects.All, RelRegOrMem.interp,
    ConstExpr.interp, Image.PeerGet.entry]
  rfl

#print axioms retry_jump
#print axioms warning_return_jump

theorem comparison_region_terms :
    Image.PeerGet.r6e = Image.PeerGet.r32 ∧ Image.PeerGet.rd4 = Image.PeerGet.rb5 :=
  ⟨rfl, rfl⟩

/-- The mirror-acceptance bound excludes both signed-warning edges after
    the successful increment. Zero is included. -/
theorem count_signs (old : Nat) (acceptedBound : old + 1 < 2^31) :
    (BitVec.ofNat 32 old).msb = false ∧ (BitVec.ofNat 32 old + 1).msb = false := by
  have oldBound : old < 2^32 := by omega
  have newBound : old + 1 < 2^32 := by omega
  simp [BitVec.msb_eq_decide, BitVec.toNat_add, Nat.mod_eq_of_lt oldBound,
    Nat.mod_eq_of_lt newBound]
  omega

#print axioms count_signs

#print axioms trace_call
#print axioms trace_region_terms
#print axioms null_guard
#print axioms refcount_load
#print axioms increment
#print axioms zero_guard
#print axioms retry_guard
#print axioms negative_guard
#print axioms overflow_guard
#print axioms clear_peer
end Binary.PeerGet
