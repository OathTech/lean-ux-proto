import CommonBitsExecution

namespace Binary.CommonBits
local instance : Labels := Image.linkedLabels

private theorem compare_word {w : Nat} (a b : BitVec w) :
    (a - b == 0#w) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

/-- The comparison and its JCC are both present in the actual history. -/
theorem family32_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t =>
      t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
      t.machine.pc = (if s.regs.get (.low .rbx .W8) == 32 then
        AllowedipsImage.CommonBits.entry + 0x4c else AllowedipsImage.CommonBits.entry + 0x26) ∧
      ∃ middle : MachineState, t.history = history ++ [middle, t.machine] ∧
        middle.pc = AllowedipsImage.CommonBits.entry + 0x24 ∧
        middle.data.regs = s.regs ∧ middle.data.dmem = s.dmem)
      ⟨⟨s, AllowedipsImage.CommonBits.entry + 0x21⟩, history⟩ := by
  have first := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x21) = some _ from rfl)
  have second := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x24) = some _ from rfl)
  simp only [historySteps, historyStep]
  rw [instructionStep, first]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp, ConstExpr.interp,
    Effects.All, StatusFlags.from_result]
  simp only [instructionStep]
  have nextPC : AllowedipsImage.CommonBits.entry + 0x21 + 3 =
      AllowedipsImage.CommonBits.entry + 0x24 := by rfl
  simp only [nextPC, second]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, Effects.All, CondCode.interp, compare_word]
  split <;> simp_all [Effects.All, AllowedipsImage.CommonBits.entry]
  all_goals rfl
/-- The comparison and its JCC are both present in the actual history. -/
theorem family128_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t =>
      t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
      t.machine.pc = (if s.regs.get (.low .rbx .W8) == 128 then
        AllowedipsImage.CommonBits.entry + 0x75 else AllowedipsImage.CommonBits.entry + 0x3e) ∧
      ∃ middle : MachineState, t.history = history ++ [middle, t.machine] ∧
        middle.pc = AllowedipsImage.CommonBits.entry + 0x3c ∧
        middle.data.regs = s.regs ∧ middle.data.dmem = s.dmem)
      ⟨⟨s, AllowedipsImage.CommonBits.entry + 0x39⟩, history⟩ := by
  have first := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x39) = some _ from rfl)
  have second := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x3c) = some _ from rfl)
  simp only [historySteps, historyStep]
  rw [instructionStep, first]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp, ConstExpr.interp,
    Effects.All, StatusFlags.from_result]
  simp only [instructionStep]
  have nextPC : AllowedipsImage.CommonBits.entry + 0x39 + 3 =
      AllowedipsImage.CommonBits.entry + 0x3c := by rfl
  simp only [nextPC, second]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, Effects.All, CondCode.interp, compare_word]
  split <;> simp_all [Effects.All, AllowedipsImage.CommonBits.entry]
  all_goals rfl
/-- The comparison and its JCC are both present in the actual history. -/
theorem high_equal_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t =>
      t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
      t.machine.pc = (if s.regs.get (.low .rbx .W64) == s.regs.get (.low .rbp .W64) then
        AllowedipsImage.CommonBits.entry + 0xc4 else AllowedipsImage.CommonBits.entry + 0x93) ∧
      ∃ middle : MachineState, t.history = history ++ [middle, t.machine] ∧
        middle.pc = AllowedipsImage.CommonBits.entry + 0x91 ∧
        middle.data.regs = s.regs ∧ middle.data.dmem = s.dmem)
      ⟨⟨s, AllowedipsImage.CommonBits.entry + 0x8e⟩, history⟩ := by
  have first := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x8e) = some _ from rfl)
  have second := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.CommonBits.entry + 0x91) = some _ from rfl)
  simp only [historySteps, historyStep]
  rw [instructionStep, first]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp, ConstExpr.interp,
    Effects.All, StatusFlags.from_result]
  simp only [instructionStep]
  have nextPC : AllowedipsImage.CommonBits.entry + 0x8e + 3 =
      AllowedipsImage.CommonBits.entry + 0x91 := by rfl
  simp only [nextPC, second]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, Effects.All, CondCode.interp, compare_word]
  split <;> simp_all [Effects.All, AllowedipsImage.CommonBits.entry]
  all_goals rfl

end Binary.CommonBits
