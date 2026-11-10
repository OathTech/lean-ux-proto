import C1TrunkFail
/-! Result C1, package 2: the straight-line regions of the two public wrappers
(`wg_allowedips_insert_v4`, `_v6`) from their entries to the CALL of `add`. -/
namespace C1Trunk
open Binary Binary.Pair Binary.Pair.Allowedips Binary.AllowedipsMutationImage
local instance : Labels := Image.linkedLabels

/-- The wrapper's four pushes: r13, r12, rbp, rbx below the return word. -/
def pushed (s : MachineData) : Mem 64 :=
  (((s.dmem.storeInt (s.regs.rsp.toBitVec-8) 8 s.regs.r13.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec-16) 8 s.regs.r12.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec-24) 8 s.regs.rbp.toBitVec.toInt).storeInt
    (s.regs.rsp.toBitVec-32) 8 s.regs.rbx.toBitVec.toInt

def prologue4Code : List (Kraken.Sized Directive) := Insert4.r00 ++ Insert4.r11.take 1
def prologue6Code : List (Kraken.Sized Directive) := Insert6.r00 ++ Insert6.r11.take 1

theorem prologue4_layout : LaidOut Insert4.fetch (Insert4.entry + .ofNat 0) prologue4Code := by
  unfold prologue4Code
  binary_layout

theorem prologue6_layout : LaidOut Insert6.fetch (Insert6.entry + .ofNat 0) prologue6Code := by
  unfold prologue6Code
  binary_layout

theorem prologue4 (s : MachineData) (pc : Int64)
    (m0 : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (m1 : (s.dmem.loadInt (s.regs.rsp.toBitVec-16) 8).isSome = true)
    (m2 : (s.dmem.loadInt (s.regs.rsp.toBitVec-24) 8).isSome = true)
    (m3 : (s.dmem.loadInt (s.regs.rsp.toBitVec-32) 8).isSome = true) :
    (Directives.interp prologue4Code s pc (fun p d => .done ⟨d,p⟩)).All (fun t =>
      t.data.regs = {s.regs with
        r13 := s.regs.rsi, r12 := s.regs.rcx,
        rbp := .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64),
        rbx := s.regs.rdi, rsp := s.regs.rsp-40} ∧
      t.data.dmem = pushed s ∧ t.pc = pc+21) := by
  have k1 := storeInt_defined s.dmem _ (s.regs.rsp.toBitVec-8) _ 8 s.regs.r13.toBitVec.toInt m1
  have k2 := storeInt_defined _ _ (s.regs.rsp.toBitVec-16) _ 8 s.regs.r12.toBitVec.toInt
    (storeInt_defined s.dmem _ (s.regs.rsp.toBitVec-8) _ 8 s.regs.r13.toBitVec.toInt m2)
  have k3 := storeInt_defined _ _ (s.regs.rsp.toBitVec-24) _ 8 s.regs.rbp.toBitVec.toInt
    (storeInt_defined _ _ (s.regs.rsp.toBitVec-16) _ 8 s.regs.r12.toBitVec.toInt
    (storeInt_defined s.dmem _ (s.regs.rsp.toBitVec-8) _ 8 s.regs.r13.toBitVec.toInt m3))
  simp only [Option.isSome_iff_exists] at m0 k1 k2 k3
  obtain ⟨v0,h0⟩ := m0
  obtain ⟨v1,h1⟩ := k1
  obtain ⟨v2,h2⟩ := k2
  obtain ⟨v3,h3⟩ := k3
  simp [prologue4Code, Insert4.r00, Insert4.r11, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, ConstExpr.interp,
    BitVec.signed,
    Effects.All, Width.bytesv, pushed, BitVec.sub_sub] at h0 h1 h2 h3 ⊢
  simp_all [Effects.All]
  simp only [Int64.add_assoc]
  congr 1

theorem prologue6 (s : MachineData) (pc : Int64)
    (m0 : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (m1 : (s.dmem.loadInt (s.regs.rsp.toBitVec-16) 8).isSome = true)
    (m2 : (s.dmem.loadInt (s.regs.rsp.toBitVec-24) 8).isSome = true)
    (m3 : (s.dmem.loadInt (s.regs.rsp.toBitVec-32) 8).isSome = true) :
    (Directives.interp prologue6Code s pc (fun p d => .done ⟨d,p⟩)).All (fun t =>
      t.data.regs = {s.regs with
        r13 := s.regs.rcx, r12 := s.regs.rsi,
        rbp := .ofBitVec ((s.regs.get (.low .rdx .W32)).setWidth 64),
        rbx := s.regs.rdi, rsp := s.regs.rsp-48} ∧
      t.data.dmem = pushed s ∧ t.pc = pc+21) := by
  have k1 := storeInt_defined s.dmem _ (s.regs.rsp.toBitVec-8) _ 8 s.regs.r13.toBitVec.toInt m1
  have k2 := storeInt_defined _ _ (s.regs.rsp.toBitVec-16) _ 8 s.regs.r12.toBitVec.toInt
    (storeInt_defined s.dmem _ (s.regs.rsp.toBitVec-8) _ 8 s.regs.r13.toBitVec.toInt m2)
  have k3 := storeInt_defined _ _ (s.regs.rsp.toBitVec-24) _ 8 s.regs.rbp.toBitVec.toInt
    (storeInt_defined _ _ (s.regs.rsp.toBitVec-16) _ 8 s.regs.r12.toBitVec.toInt
    (storeInt_defined s.dmem _ (s.regs.rsp.toBitVec-8) _ 8 s.regs.r13.toBitVec.toInt m3))
  simp only [Option.isSome_iff_exists] at m0 k1 k2 k3
  obtain ⟨v0,h0⟩ := m0
  obtain ⟨v1,h1⟩ := k1
  obtain ⟨v2,h2⟩ := k2
  obtain ⟨v3,h3⟩ := k3
  simp [prologue6Code, Insert6.r00, Insert6.r11, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, Reg64s.set, Reg64s.set64,
    BitVec.drop, BitVec.take, ConstExpr.interp,
    BitVec.signed,
    Effects.All, Width.bytesv, pushed, BitVec.sub_sub] at h0 h1 h2 h3 ⊢
  simp_all [Effects.All]
  simp only [Int64.add_assoc]
  congr 1

theorem swap32_wide (n : BitVec 32) :
    BitVec.extractLsb' 0 8 (BitVec.setWidth 64 (BitVec.setWidth 32 n)) ++
      BitVec.extractLsb' 8 8 (BitVec.setWidth 64 (BitVec.setWidth 32 n)) ++
      BitVec.extractLsb' 16 8 (BitVec.setWidth 64 (BitVec.setWidth 32 n)) ++
      BitVec.extractLsb' 24 8 (BitVec.setWidth 64 (BitVec.setWidth 32 n)) = Allowedips.swap32 n := by
  have wide : (BitVec.setWidth 64 n).toNat = n.toNat := by
    have bound := n.isLt
    simp only [BitVec.toNat_setWidth]
    omega
  apply BitVec.eq_of_toNat_eq
  simp only [Allowedips.swap32, BitVec.toNat_append, BitVec.extractLsb'_toNat, BitVec.setWidth_eq, wide]

theorem store32_value (x : BitVec 32) :
    ((x.toNat : Int) % 18446744073709551616).bmod 4294967296 = x.toInt := by
  have bound := x.isLt
  rw [Int.emod_eq_of_lt (by omega) (by omega), BitVec.toInt_eq_toNat_bmod]

def body4Code : List (Kraken.Sized Directive) := Insert4.r1a.drop 1 ++ Insert4.r39

theorem body4_layout : LaidOut Insert4.fetch (Insert4.entry + .ofNat 31) body4Code := by
  unfold body4Code
  binary_layout

/-- v4, after the increment: the arguments of `add`, the address word loaded
in network order and stored in host order at `rsp+4`, and the CALL. -/
theorem body4 (s : MachineData) (network : BitVec 32) (old0 old1 : Int)
    (input : s.dmem.loadInt s.regs.r13.toBitVec 4 = some (network.toNat : Int))
    (mapped : s.dmem.loadInt (s.regs.rsp.toBitVec+4) 4 = some old0)
    (word : (s.dmem.storeInt (s.regs.rsp.toBitVec+4) 4 (Allowedips.swap32 network).toInt).loadInt
      (s.regs.rsp.toBitVec-8) 8 = some old1) :
    (Directives.interp body4Code s (Insert4.entry+.ofNat 31) (fun p d => .done ⟨d,p⟩)).All (fun t =>
      t.data.regs = {s.regs with
        r8 := s.regs.r12, rdi := s.regs.rbx,
        rax := .ofBitVec ((Allowedips.swap32 network).setWidth 64),
        rcx := .ofBitVec ((s.regs.get (.low .rbp .W8)).setWidth 64),
        rdx := s.regs.rsp+4, rsi := 0x20, rsp := s.regs.rsp-8} ∧
      t.data.dmem = (s.dmem.storeInt (s.regs.rsp.toBitVec+4) 4 (Allowedips.swap32 network).toInt).storeInt
        (s.regs.rsp.toBitVec-8) 8 (Insert4.entry+.ofNat 0x42).toBitVec.toInt ∧
      t.pc = Add.entry) := by
  have target : label "L_ffffffff813a0bc0" = Add.entry := by decide
  simp [body4Code, Insert4.r1a, Insert4.r39, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt, BitVec.ofInt_add,
    BitVec.ofInt_ofNat, Effects.All, target] at input mapped word ⊢
  rw [input]
  simp only [Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  simp only [mapped, Effects.All, swap32_wide, store32_value, Width.bytesv]
  have bytes : BitVec.ofNat 64 Width.W64.bytes = 8#64 := rfl
  simp only [bytes, word, Effects.All]
  simp [Insert4.entry, Add.entry]

def pre6Code : List (Kraken.Sized Directive) := Insert6.r1a.take 3
def body6Code : List (Kraken.Sized Directive) := Insert6.r1a.drop 4 ++ Insert6.r39

theorem pre6_layout : LaidOut Insert6.fetch (Insert6.entry + .ofNat 26) pre6Code := by
  unfold pre6Code
  binary_layout

theorem body6_layout : LaidOut Insert6.fetch (Insert6.entry + .ofNat 42) body6Code := by
  unfold body6Code
  binary_layout

/-- v6, before the increment: three of `add`'s arguments. -/
theorem pre6 (s : MachineData) (pc : Int64) :
    (Directives.interp pre6Code s pc (fun p d => .done ⟨d,p⟩)).All (fun t =>
      t.data.regs = {s.regs with
        rcx := .ofBitVec ((s.regs.get (.low .rbp .W8)).setWidth 64),
        rdi := s.regs.rbx+8, r8 := s.regs.r13} ∧
      t.data.dmem = s.dmem ∧ t.pc = pc+11) := by
  simp [pre6Code, Insert6.r1a, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.set, MachineData.setReg,
    AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, Effects.All]
  constructor
  · apply UInt64.toBitVec_inj.mp
    simp [BitVec.ofInt_add, UInt64.toBitVec_add]
  · simp only [Int64.add_assoc]
    congr 1

def high6 (s : MachineData) (high : BitVec 64) : Mem 64 :=
  s.dmem.storeInt s.regs.rsp.toBitVec 8 (Allowedips.swap64 high).toInt

def low6 (s : MachineData) (high low : BitVec 64) : Mem 64 :=
  (high6 s high).storeInt (s.regs.rsp.toBitVec+8) 8 (Allowedips.swap64 low).toInt

/-- v6, after the increment: the two address words loaded in network order
and stored in host order at `rsp` and `rsp+8`, and the CALL. -/
theorem body6 (s : MachineData) (high low : BitVec 64) (old0 old1 old2 : Int)
    (inputHigh : s.dmem.loadInt s.regs.r12.toBitVec 8 = some (high.toNat : Int))
    (mappedHigh : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some old0)
    (inputLow : (high6 s high).loadInt (s.regs.r12.toBitVec+8) 8 = some (low.toNat : Int))
    (mappedLow : (high6 s high).loadInt (s.regs.rsp.toBitVec+8) 8 = some old1)
    (word : (low6 s high low).loadInt (s.regs.rsp.toBitVec-8) 8 = some old2) :
    (Directives.interp body6Code s (Insert6.entry+.ofNat 42) (fun p d => .done ⟨d,p⟩)).All (fun t =>
      t.data.regs = {s.regs with
        rax := .ofBitVec (Allowedips.swap64 low),
        rdx := s.regs.rsp, rsi := 0x80, rsp := s.regs.rsp-8} ∧
      t.data.dmem = (low6 s high low).storeInt
        (s.regs.rsp.toBitVec-8) 8 (Insert6.entry+.ofNat 0x4f).toBitVec.toInt ∧
      t.pc = Add.entry) := by
  have target : label "L_ffffffff813a0bc0" = Add.entry := by decide
  simp [body6Code, Insert6.r1a, Insert6.r39, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt, BitVec.ofInt_add,
    BitVec.ofInt_ofNat, Effects.All, target] at inputHigh mappedHigh ⊢
  rw [inputHigh]
  simp only [Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, mappedHigh]
  simp only [high6, low6, Allowedips.swap64] at inputLow mappedLow word ⊢
  simp only [BitVec.ofNat_eq_ofNat] at *
  simp only [inputLow, Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    mappedLow, Width.bytesv, word]
  simp [Insert6.entry, Add.entry]

#print axioms prologue4
#print axioms prologue6
#print axioms body4
#print axioms pre6
#print axioms body6
end C1Trunk
