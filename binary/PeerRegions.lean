import Regions

namespace Binary.PeerGet
local instance : Labels := Image.linkedLabels

private theorem u64_zero (v : UInt64) : v.toBitVec = 0#64 ↔ v = 0 :=
  UInt64.toBitVec_inj

def run (code : List (Kraken.Sized Directive)) (offset : Nat) (s : MachineData) : Effects :=
  Directives.interp code s (Image.PeerGet.entry + .ofNat offset) (fun p d => .done ⟨d, p⟩)

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

#print axioms null_guard
#print axioms zero_guard
#print axioms retry_guard
#print axioms negative_guard
#print axioms overflow_guard
#print axioms clear_peer
end Binary.PeerGet
