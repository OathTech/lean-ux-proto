import AllowedipsImage
import Memory
import Kraken.X64.OmniSemantics
namespace Binary.Allowedips
local instance : Labels := Image.linkedLabels

def run (code : List (Kraken.Sized Directive)) (offset : Nat) (s : MachineData) : Effects :=
  Directives.interp code s (AllowedipsImage.Lookup.entry + .ofNat offset)
    (fun p d => .done ⟨d, p⟩)

private theorem compare_eq {w : Nat} (a b : BitVec w) :
    (a - b == 0#w) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

theorem family32 (s : MachineData) :
    (run AllowedipsImage.Lookup.r3e 0x3e s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbx .W8) == 32 then
        AllowedipsImage.Lookup.entry + 0x171 else AllowedipsImage.Lookup.entry + 0x47) := by
  simp [run, AllowedipsImage.Lookup.r3e, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     ConstExpr.interp, Effects.All, StatusFlags.from_result,
    CondCode.interp, compare_eq]
  split <;> simp_all [Effects.All, AllowedipsImage.Lookup.entry] <;> rfl

theorem family128 (s : MachineData) :
    (run AllowedipsImage.Lookup.r58 0x58 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .rbx .W8) == 128 then
        AllowedipsImage.Lookup.entry + 0x14f else AllowedipsImage.Lookup.entry + 0x61) := by
  simp [run, AllowedipsImage.Lookup.r58, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
     ConstExpr.interp, Effects.All, StatusFlags.from_result,
    CondCode.interp, compare_eq]
  split <;> simp_all [Effects.All, AllowedipsImage.Lookup.entry] <;> rfl

theorem fullLength (s : MachineData) :
    (run AllowedipsImage.Lookup.raf 0xaf s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.get (.low .r12 .W8) == s.regs.get (.low .r15 .W8) then
        AllowedipsImage.Lookup.entry + 0x101 else AllowedipsImage.Lookup.entry + 0xb4) := by
  simp [run, AllowedipsImage.Lookup.raf, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
      Effects.All, StatusFlags.from_result,
    CondCode.interp, compare_eq]
  split <;> simp_all [Effects.All, AllowedipsImage.Lookup.entry] <;> rfl

theorem rootGuard (s : MachineData) :
    (run (AllowedipsImage.Lookup.r79.drop 1) 0x7e s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.rbx.toBitVec == 0 then
        AllowedipsImage.Lookup.entry + 0x184 else AllowedipsImage.Lookup.entry + 0x87) := by
  simp [run, AllowedipsImage.Lookup.r79,

    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.interp, Operand.interp, Effects.All, StatusFlags.from_result,
    CondCode.interp, BitVec.and_self, Reg64s.get, Reg64s.get64, Reg.base,
    Reg.offset, BitVec.take, BitVec.drop]
  by_cases zero : s.regs.rbx.toBitVec = 0 <;>
    simp_all [Effects.All, AllowedipsImage.Lookup.entry] <;> rfl

theorem nextGuard (s : MachineData) :
    (run (AllowedipsImage.Lookup.rb9.drop 6) 0xd0 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.rbx.toBitVec == 0 then
        AllowedipsImage.Lookup.entry + 0x101 else AllowedipsImage.Lookup.entry + 0xd5) := by
  simp [run,  AllowedipsImage.Lookup.rb9,

    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.interp, Operand.interp, Effects.All, StatusFlags.from_result,
    CondCode.interp, BitVec.and_self, Reg64s.get, Reg64s.get64, Reg.base,
    Reg.offset, BitVec.take, BitVec.drop]
  by_cases zero : s.regs.rbx.toBitVec = 0 <;>
    simp_all [Effects.All, AllowedipsImage.Lookup.entry] <;> rfl

theorem foundGuard (s : MachineData) :
    (run AllowedipsImage.Lookup.r106 0x106 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.rbp.toBitVec == 0 then
        AllowedipsImage.Lookup.entry + 0x184 else AllowedipsImage.Lookup.entry + 0x10b) := by
  simp [run,
    AllowedipsImage.Lookup.r106,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.interp, Operand.interp, Effects.All, StatusFlags.from_result,
    CondCode.interp, BitVec.and_self, Reg64s.get, Reg64s.get64, Reg.base,
    Reg.offset, BitVec.take, BitVec.drop]
  by_cases zero : s.regs.rbp.toBitVec = 0 <;>
    simp_all [Effects.All, AllowedipsImage.Lookup.entry] <;> rfl

theorem peerGuard (s : MachineData) :
    (run AllowedipsImage.Lookup.r119 0x119 s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if s.regs.rax.toBitVec == 0 then
        AllowedipsImage.Lookup.entry + 0x74 else AllowedipsImage.Lookup.entry + 0x122) := by
  simp [run,
     AllowedipsImage.Lookup.r119,
    Directives.interp, Directive.interp, Instr.interp, Operation.interp,
    RegOrMem.interp, Operand.interp, Effects.All, StatusFlags.from_result,
    CondCode.interp, BitVec.and_self, Reg64s.get, Reg64s.get64, Reg.base,
    Reg.offset, BitVec.take, BitVec.drop]
  by_cases zero : s.regs.rax.toBitVec = 0 <;>
    simp_all [Effects.All, AllowedipsImage.Lookup.entry] <;> rfl

#print axioms family32
#print axioms family128
#print axioms fullLength
#print axioms rootGuard
#print axioms nextGuard
#print axioms foundGuard
#print axioms peerGuard
theorem carry8 (a b : BitVec 8) :
    ((a-b).unsigned != a.unsigned-b.unsigned) = decide (a.toNat < b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp only [bne_iff_ne, decide_eq_true_eq, BitVec.unsigned, BitVec.toNat_sub]
  have ha := a.isLt
  have hb := b.isLt
  omega

/-- Unsigned byte comparison is exactly the prefix-length comparison. -/
theorem prefixGuard (s : MachineData) :
    (run AllowedipsImage.Lookup.rfc 0xfc s).All (fun t =>
      t.data.regs = s.regs ∧ t.data.dmem = s.dmem ∧
      t.pc = if (s.regs.get (.low .r15 .W8)).toNat ≤
          (s.regs.get (.low .r14 .W8)).toNat then
        AllowedipsImage.Lookup.entry + 0x90 else AllowedipsImage.Lookup.entry + 0x101) := by
  simp [run, AllowedipsImage.Lookup.rfc, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
      Effects.All, StatusFlags.from_result,
    CondCode.interp, carry8]
  split <;> simp_all [Effects.All, AllowedipsImage.Lookup.entry] <;> rfl

/-- CMOVNE records whether the node has a peer even without a branch. -/
theorem hasPeer (s : MachineData) (peer : BitVec 64)
    (field : s.dmem.loadInt s.regs.rbx.toBitVec 8 = some peer.toNat) :
    (run (AllowedipsImage.Lookup.r95.take 3) 0x95 s).All (fun t =>
      t.data.regs = {s.regs with
        rax := .ofBitVec peer, rbp := (if peer == 0 then s.regs.rbp else s.regs.rbx)} ∧
      t.data.dmem = s.dmem ∧ t.pc = AllowedipsImage.Lookup.entry + 0x9f) := by
  simp [run, AllowedipsImage.Lookup.r95, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg, AddrExpr.interp,
    ConstExpr.interp, Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt,
    Effects.All, StatusFlags.from_result, CondCode.interp, BitVec.and_self,
    AllowedipsImage.Lookup.entry] at field ⊢
  rw [field]
  simp [Effects.All, BitVec.ofInt_natCast, BitVec.ofNat_toNat]
  split <;> simp_all

/-- The no-match exit returns zero through the common epilogue. -/
theorem noMatch (s : MachineData) :
    (run AllowedipsImage.Lookup.r184 0x184 s).All (fun t =>
      t.data.regs = {s.regs with rax := 0} ∧ t.data.dmem = s.dmem ∧
      t.pc = AllowedipsImage.Lookup.entry + 0x122) := by
  have target : label "L_ffffffff813a0952" = AllowedipsImage.Lookup.entry+0x122 := by decide
  simp [run, AllowedipsImage.Lookup.r184, Directives.interp, Directive.interp,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    RelRegOrMem.interp, ConstExpr.interp, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64, Reg.base, Reg.offset,
    BitVec.take, BitVec.drop, Effects.All, target, AllowedipsImage.Lookup.entry]

#print axioms prefixGuard
#print axioms hasPeer
#print axioms noMatch
end Binary.Allowedips
