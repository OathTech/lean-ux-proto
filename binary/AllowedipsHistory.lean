import AllowedipsRegions
import HistoryRegions
import AllowedipsObservation

namespace Binary.Allowedips
open LookupHistory
local instance : Labels := Image.linkedLabels

theorem root_guard_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rbx .W64) s
      (AllowedipsImage.Lookup.entry+0x81)
      (if s.regs.get (.low .rbx .W64) == 0 then AllowedipsImage.Lookup.entry+0x184
       else AllowedipsImage.Lookup.entry+0x87) history)
      ⟨⟨s, AllowedipsImage.Lookup.entry+0x7e⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff813a09b4" 3 6 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms root_guard_history

theorem next_guard_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rbx .W64) s
      (AllowedipsImage.Lookup.entry+0xd3)
      (if s.regs.get (.low .rbx .W64) == 0 then AllowedipsImage.Lookup.entry+0x101
       else AllowedipsImage.Lookup.entry+0xd5) history)
      ⟨⟨s, AllowedipsImage.Lookup.entry+0xd0⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff813a0931" 3 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms next_guard_history

theorem found_guard_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rbp .W64) s
      (AllowedipsImage.Lookup.entry+0x109)
      (if s.regs.get (.low .rbp .W64) == 0 then AllowedipsImage.Lookup.entry+0x184
       else AllowedipsImage.Lookup.entry+0x10b) history)
      ⟨⟨s, AllowedipsImage.Lookup.entry+0x106⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff813a09b4" 3 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms found_guard_history

theorem peer_guard_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rax .W64) s
      (AllowedipsImage.Lookup.entry+0x11c)
      (if s.regs.get (.low .rax .W64) == 0 then AllowedipsImage.Lookup.entry+0x74
       else AllowedipsImage.Lookup.entry+0x122) history)
      ⟨⟨s, AllowedipsImage.Lookup.entry+0x119⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff813a08a4" 3 6 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms peer_guard_history


private theorem compare_byte (a b : BitVec 8) : (a-b == 0) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add]

theorem family32_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t =>
      t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
      t.machine.pc = (if s.regs.get (.low .rbx .W8) == 32 then
        AllowedipsImage.Lookup.entry+0x171 else AllowedipsImage.Lookup.entry+0x47) ∧
      ∃ middle : MachineState, t.history = history ++ [middle,t.machine] ∧
        middle.pc = AllowedipsImage.Lookup.entry+0x41 ∧
        middle.data.regs = s.regs ∧ middle.data.dmem = s.dmem)
      ⟨⟨s, AllowedipsImage.Lookup.entry+0x3e⟩,history⟩ := by
  have first := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x3e) = some _ from rfl)
  have second := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x41) = some _ from rfl)
  simp only [historySteps, historyStep]
  rw [instructionStep, first]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp, ConstExpr.interp,
    Effects.All, StatusFlags.from_result]
  simp only [instructionStep]
  have nextPC : AllowedipsImage.Lookup.entry+0x3e+3 = AllowedipsImage.Lookup.entry+0x41 := rfl
  simp only [nextPC, second]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, Effects.All, CondCode.interp]
  split <;> simp_all [Effects.All, AllowedipsImage.Lookup.entry, BitVec.sub_eq_iff_eq_add]
  all_goals rfl

#print axioms family32_history

theorem family128_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t =>
      t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
      t.machine.pc = (if s.regs.get (.low .rbx .W8) == 128 then
        AllowedipsImage.Lookup.entry+0x14f else AllowedipsImage.Lookup.entry+0x61) ∧
      ∃ middle : MachineState, t.history = history ++ [middle,t.machine] ∧
        middle.pc = AllowedipsImage.Lookup.entry+0x5b ∧
        middle.data.regs = s.regs ∧ middle.data.dmem = s.dmem)
      ⟨⟨s, AllowedipsImage.Lookup.entry+0x58⟩,history⟩ := by
  have first := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x58) = some _ from rfl)
  have second := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0x5b) = some _ from rfl)
  simp only [historySteps, historyStep]
  rw [instructionStep, first]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp, ConstExpr.interp,
    Effects.All, StatusFlags.from_result]
  simp only [instructionStep]
  have nextPC : AllowedipsImage.Lookup.entry+0x58+3 = AllowedipsImage.Lookup.entry+0x5b := rfl
  simp only [nextPC, second]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, Effects.All, CondCode.interp]
  split <;> simp_all [Effects.All, AllowedipsImage.Lookup.entry, BitVec.sub_eq_iff_eq_add]
  all_goals rfl

#print axioms family128_history

theorem fullLength_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t =>
      t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
      t.machine.pc = (if s.regs.get (.low .r12 .W8) == s.regs.get (.low .r15 .W8) then
        AllowedipsImage.Lookup.entry+0x101 else AllowedipsImage.Lookup.entry+0xb4) ∧
      ∃ middle : MachineState, t.history = history ++ [middle,t.machine] ∧
        middle.pc = AllowedipsImage.Lookup.entry+0xb2 ∧
        middle.data.regs = s.regs ∧ middle.data.dmem = s.dmem)
      ⟨⟨s, AllowedipsImage.Lookup.entry+0xaf⟩,history⟩ := by
  have first := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0xaf) = some _ from rfl)
  have second := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0xb2) = some _ from rfl)
  simp only [historySteps, historyStep]
  rw [instructionStep, first]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result]
  simp only [instructionStep]
  have nextPC : AllowedipsImage.Lookup.entry+0xaf+3 = AllowedipsImage.Lookup.entry+0xb2 := rfl
  simp only [nextPC, second]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, Effects.All, CondCode.interp]
  split <;> simp_all [Effects.All, AllowedipsImage.Lookup.entry, BitVec.sub_eq_iff_eq_add]
  all_goals rfl

#print axioms fullLength_history

theorem prefix_history (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, AllowedipsImage.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t =>
      t.machine.data.regs = s.regs ∧ t.machine.data.dmem = s.dmem ∧
      t.machine.pc = (if (s.regs.get (.low .r15 .W8)).toNat ≤ (s.regs.get (.low .r14 .W8)).toNat then
        AllowedipsImage.Lookup.entry+0x90 else AllowedipsImage.Lookup.entry+0x101) ∧
      ∃ middle : MachineState, t.history = history ++ [middle,t.machine] ∧
        middle.pc = AllowedipsImage.Lookup.entry+0xff ∧
        middle.data.regs = s.regs ∧ middle.data.dmem = s.dmem)
      ⟨⟨s, AllowedipsImage.Lookup.entry+0xfc⟩,history⟩ := by
  have first := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0xfc) = some _ from rfl)
  have second := agree _ _ (show AllowedipsImage.fetch (AllowedipsImage.Lookup.entry+0xff) = some _ from rfl)
  simp only [historySteps, historyStep]
  rw [instructionStep, first]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    Effects.All, StatusFlags.from_result]
  simp only [instructionStep]
  have nextPC : AllowedipsImage.Lookup.entry+0xfc+3 = AllowedipsImage.Lookup.entry+0xff := rfl
  simp only [nextPC, second]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, Effects.All, CondCode.interp,  carry8]
  split <;> simp_all [Effects.All, AllowedipsImage.Lookup.entry]
  all_goals rfl

#print axioms prefix_history

end Binary.Allowedips
