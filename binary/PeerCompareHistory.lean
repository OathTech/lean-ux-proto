import PeerClearHistory
import LookupLoads

namespace Binary.PeerGet
local instance : Labels := Image.linkedLabels

def xorMoved (s : MachineData) (zero dst src : Reg .W32) (af : Bool) : MachineData :=
  let first := zeroed s zero af
  first.setReg dst (first.regs.get src)

/-- Two physical setup instructions, before their actual comparison CALL.
    Keeping the first successor matters when it emits a folded decision. -/
theorem xor_mov_history (fetch : Int64 → Option Decoded) (pc : Int64)
    (zero dst src : Reg .W32) (firstSize secondSize : Nat)
    (firstPositive : 0 < firstSize) (secondPositive : 0 < secondSize)
    (first : fetch pc = some ⟨.regular .W64 .W32
      (.xor (.reg zero) (.regOrMem (.reg zero))), firstSize⟩)
    (second : fetch (pc + .ofNat firstSize) = some ⟨.regular .W64 .W32
      (.mov (.reg dst) (.regOrMem (.reg src))), secondSize⟩)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨xorMoved s zero dst src af, pc + .ofNat firstSize + .ofNat secondSize⟩ ∧
      t.history = history ++ [⟨zeroed s zero af, pc + .ofNat firstSize⟩, t.machine])
      ⟨⟨s, pc⟩, history⟩ := by
  rw [show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _
    (xor32_history fetch pc firstSize zero firstPositive first s history)
  rintro t ⟨af, machine, recorded⟩
  have cursor : t = ⟨⟨zeroed s zero af, pc + .ofNat firstSize⟩,
      history ++ [⟨zeroed s zero af, pc + .ofNat firstSize⟩]⟩ := by cases t; simp_all
  rw [cursor]
  have step := LookupHistory.mov32_history fetch (pc + .ofNat firstSize) dst src secondSize
    secondPositive second (zeroed s zero af)
    (history ++ [(⟨zeroed s zero af, pc + .ofNat firstSize⟩ : MachineState)])
  apply historySteps_mono fetch 1 _ _ _ _ step
  rintro final ⟨machine, recorded⟩
  exact ⟨af, machine, by simpa only [List.append_assoc, List.singleton_append] using recorded⟩

theorem xor_xor_history (fetch : Int64 → Option Decoded) (pc : Int64)
    (firstReg secondReg : Reg .W32) (firstSize secondSize : Nat)
    (firstPositive : 0 < firstSize) (secondPositive : 0 < secondSize)
    (first : fetch pc = some ⟨.regular .W64 .W32
      (.xor (.reg firstReg) (.regOrMem (.reg firstReg))), firstSize⟩)
    (second : fetch (pc + .ofNat firstSize) = some ⟨.regular .W64 .W32
      (.xor (.reg secondReg) (.regOrMem (.reg secondReg))), secondSize⟩)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af₁ af₂,
      t.machine = ⟨zeroed (zeroed s firstReg af₁) secondReg af₂,
        pc + .ofNat firstSize + .ofNat secondSize⟩ ∧
      t.history = history ++ [⟨zeroed s firstReg af₁, pc + .ofNat firstSize⟩, t.machine])
      ⟨⟨s, pc⟩, history⟩ := by
  rw [show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _
    (xor32_history fetch pc firstSize firstReg firstPositive first s history)
  rintro t ⟨af₁, machine, recorded⟩
  have cursor : t = ⟨⟨zeroed s firstReg af₁, pc + .ofNat firstSize⟩,
      history ++ [⟨zeroed s firstReg af₁, pc + .ofNat firstSize⟩]⟩ := by cases t; simp_all
  rw [cursor]
  have step := xor32_history fetch (pc + .ofNat firstSize) secondSize secondReg secondPositive second
    (zeroed s firstReg af₁) (history ++ [(⟨zeroed s firstReg af₁, pc + .ofNat firstSize⟩ : MachineState)])
  apply historySteps_mono fetch 1 _ _ _ _ step
  rintro final ⟨af₂, machine, recorded⟩
  exact ⟨af₁, af₂, machine, by simpa only [List.append_assoc, List.singleton_append] using recorded⟩

/-- Register-to-register MOV followed by XOR, as on the live result path. -/
theorem mov_xor_history (fetch : Int64 → Option Decoded) (pc : Int64)
    (dst src zero : Reg .W32) (firstSize secondSize : Nat)
    (firstPositive : 0 < firstSize) (secondPositive : 0 < secondSize)
    (first : fetch pc = some ⟨.regular .W64 .W32
      (.mov (.reg dst) (.regOrMem (.reg src))), firstSize⟩)
    (second : fetch (pc + .ofNat firstSize) = some ⟨.regular .W64 .W32
      (.xor (.reg zero) (.regOrMem (.reg zero))), secondSize⟩)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨zeroed (s.setReg dst (s.regs.get src)) zero af,
        pc + .ofNat firstSize + .ofNat secondSize⟩ ∧
      t.history = history ++ [⟨s.setReg dst (s.regs.get src), pc + .ofNat firstSize⟩, t.machine])
      ⟨⟨s, pc⟩, history⟩ := by
  rw [show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _
    (LookupHistory.mov32_history fetch pc dst src firstSize firstPositive first s history)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨s.setReg dst (s.regs.get src), pc + .ofNat firstSize⟩,
      history ++ [⟨s.setReg dst (s.regs.get src), pc + .ofNat firstSize⟩]⟩ := by cases t; simp_all
  rw [cursor]
  have step := xor32_history fetch (pc + .ofNat firstSize) secondSize zero secondPositive second
    (s.setReg dst (s.regs.get src))
    (history ++ [(⟨s.setReg dst (s.regs.get src), pc + .ofNat firstSize⟩ : MachineState)])
  apply historySteps_mono fetch 1 _ _ _ _ step
  rintro final ⟨af, machine, recorded⟩
  exact ⟨af, machine, by simpa only [List.append_assoc, List.singleton_append] using recorded⟩

/-- Actual setup at +0x32, stopping before its comparison CALL. -/
theorem old_arguments_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨xorMoved s (.low .rdi .W32) (.low .rsi .W32) (.low .rbp .W32) af,
        Image.PeerGet.entry+0x36⟩ ∧
      t.history = history ++ [⟨zeroed s (.low .rdi .W32) af, Image.PeerGet.entry+0x34⟩, t.machine])
      ⟨⟨s, Image.PeerGet.entry+0x32⟩, history⟩ := by
  simpa [Int64.add_assoc, Image.PeerGet.entry] using
    xor_mov_history fetch (Image.PeerGet.entry+0x32)
      (.low .rdi .W32) (.low .rsi .W32) (.low .rbp .W32) 2 2
      (by decide) (by decide) (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms old_arguments_history

/-- Actual setup at +0x6e, stopping before its comparison CALL. -/
theorem negative_arguments_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨xorMoved s (.low .rdi .W32) (.low .rsi .W32) (.low .rbp .W32) af,
        Image.PeerGet.entry+0x72⟩ ∧
      t.history = history ++ [⟨zeroed s (.low .rdi .W32) af, Image.PeerGet.entry+0x70⟩, t.machine])
      ⟨⟨s, Image.PeerGet.entry+0x6e⟩, history⟩ := by
  simpa [Int64.add_assoc, Image.PeerGet.entry] using
    xor_mov_history fetch (Image.PeerGet.entry+0x6e)
      (.low .rdi .W32) (.low .rsi .W32) (.low .rbp .W32) 2 2
      (by decide) (by decide) (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms negative_arguments_history

/-- Actual setup at +0x80, stopping before its comparison CALL. -/
theorem wrap_arguments_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨xorMoved s (.low .rdi .W32) (.low .rsi .W32) (.low .r12 .W32) af,
        Image.PeerGet.entry+0x85⟩ ∧
      t.history = history ++ [⟨zeroed s (.low .rdi .W32) af, Image.PeerGet.entry+0x82⟩, t.machine])
      ⟨⟨s, Image.PeerGet.entry+0x80⟩, history⟩ := by
  simpa [Int64.add_assoc, Image.PeerGet.entry] using
    xor_mov_history fetch (Image.PeerGet.entry+0x80)
      (.low .rdi .W32) (.low .rsi .W32) (.low .r12 .W32) 2 3
      (by decide) (by decide) (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms wrap_arguments_history

/-- Both undefined XOR flags remain in the actual setup history. -/
theorem dead_negative_arguments_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af₁ af₂,
      t.machine = ⟨zeroed (zeroed s (.low .rsi .W32) af₁) (.low .rdi .W32) af₂,
        Image.PeerGet.entry+0xb9⟩ ∧
      t.history = history ++ [⟨zeroed s (.low .rsi .W32) af₁, Image.PeerGet.entry+0xb7⟩, t.machine])
      ⟨⟨s, Image.PeerGet.entry+0xb5⟩, history⟩ := by
  simpa [Int64.add_assoc, Image.PeerGet.entry] using
    xor_xor_history fetch (Image.PeerGet.entry+0xb5)
      (.low .rsi .W32) (.low .rdi .W32) 2 2
      (by decide) (by decide) (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms dead_negative_arguments_history

/-- Both undefined XOR flags remain in the actual setup history. -/
theorem dead_result_arguments_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af₁ af₂,
      t.machine = ⟨zeroed (zeroed s (.low .rsi .W32) af₁) (.low .rdi .W32) af₂,
        Image.PeerGet.entry+0xd8⟩ ∧
      t.history = history ++ [⟨zeroed s (.low .rsi .W32) af₁, Image.PeerGet.entry+0xd6⟩, t.machine])
      ⟨⟨s, Image.PeerGet.entry+0xd4⟩, history⟩ := by
  simpa [Int64.add_assoc, Image.PeerGet.entry] using
    xor_xor_history fetch (Image.PeerGet.entry+0xd4)
      (.low .rsi .W32) (.low .rdi .W32) 2 2
      (by decide) (by decide) (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms dead_result_arguments_history

theorem live_result_arguments_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨zeroed (s.setReg (.low .rsi .W32) (s.regs.get (.low .rbp .W32)))
        (.low .rdi .W32) af, Image.PeerGet.entry+0x98⟩ ∧
      t.history = history ++ [⟨s.setReg (.low .rsi .W32) (s.regs.get (.low .rbp .W32)),
        Image.PeerGet.entry+0x96⟩, t.machine])
      ⟨⟨s, Image.PeerGet.entry+0x94⟩, history⟩ := by
  simpa [Int64.add_assoc, Image.PeerGet.entry] using
    mov_xor_history fetch (Image.PeerGet.entry+0x94)
      (.low .rsi .W32) (.low .rbp .W32) (.low .rdi .W32) 2 2
      (by decide) (by decide) (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms live_result_arguments_history

def oneArgument (s : MachineData) : MachineData := s.setReg (.low .rsi .W32) 1

theorem dead_wrap_arguments_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨zeroed (oneArgument s) (.low .rdi .W32) af, Image.PeerGet.entry+0xca⟩ ∧
      t.history = history ++ [⟨oneArgument s, Image.PeerGet.entry+0xc8⟩, t.machine])
      ⟨⟨s, Image.PeerGet.entry+0xc3⟩, history⟩ := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xc3) = some _ from rfl)
  have first : instructionStep fetch ⟨s, Image.PeerGet.entry+0xc3⟩
      (fun t => t = ⟨oneArgument s, Image.PeerGet.entry+0xc8⟩) := by
    simp only [instructionStep, here]
    refine ⟨by decide, ?_⟩
    simp [Instr.interp, Operation.interp, Operand.interp, ConstExpr.interp,
      MachineData.set, Effects.All, oneArgument]
    rfl
  rw [show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _
    (instruction_history fetch ⟨s, Image.PeerGet.entry+0xc3⟩ history _ first)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨oneArgument s, Image.PeerGet.entry+0xc8⟩,
      history ++ [⟨oneArgument s, Image.PeerGet.entry+0xc8⟩]⟩ := by cases t; simp_all
  rw [cursor]
  have second := xor32_history fetch (Image.PeerGet.entry+0xc8) 2 (.low .rdi .W32)
    (by decide) (agree _ _ (by rfl)) (oneArgument s)
    (history ++ [(⟨oneArgument s, Image.PeerGet.entry+0xc8⟩ : MachineState)])
  apply historySteps_mono fetch 1 _ _ _ _ second
  rintro final ⟨af, machine, recorded⟩
  exact ⟨af, machine, by simpa only [List.append_assoc, List.singleton_append] using recorded⟩

theorem dead_negative_observed (rxSection : Nat) (s : MachineData) (af₁ af₂ : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.PeerGet.entry+0xb5⟩,
       ⟨zeroed s (.low .rsi .W32) af₁, Image.PeerGet.entry+0xb7⟩,
       ⟨zeroed (zeroed s (.low .rsi .W32) af₁) (.low .rdi .W32) af₂, Image.PeerGet.entry+0xb9⟩] =
      .ok [LookupObservation.decision rxSection .refcountAddNzNegative false
        ⟨zeroed s (.low .rsi .W32) af₁, Image.PeerGet.entry+0xb7⟩] := by
  simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  rfl

#print axioms dead_negative_observed

theorem dead_result_observed (rxSection : Nat) (s : MachineData) (af₁ af₂ : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.PeerGet.entry+0xd4⟩,
       ⟨zeroed s (.low .rsi .W32) af₁, Image.PeerGet.entry+0xd6⟩,
       ⟨zeroed (zeroed s (.low .rsi .W32) af₁) (.low .rdi .W32) af₂, Image.PeerGet.entry+0xd8⟩] =
      .ok [LookupObservation.decision rxSection .peerGetMaybeZeroDead true
        ⟨zeroed s (.low .rsi .W32) af₁, Image.PeerGet.entry+0xd6⟩] := by
  simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  rfl

#print axioms dead_result_observed

theorem dead_wrap_observed (rxSection : Nat) (s : MachineData) (af : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.PeerGet.entry+0xc3⟩, ⟨oneArgument s, Image.PeerGet.entry+0xc8⟩,
       ⟨zeroed (oneArgument s) (.low .rdi .W32) af, Image.PeerGet.entry+0xca⟩] =
      .ok [LookupObservation.decision rxSection .refcountAddNzWraps false
        ⟨oneArgument s, Image.PeerGet.entry+0xc8⟩] := by
  simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  rfl

theorem live_result_observed (rxSection : Nat) (s : MachineData) (af : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.PeerGet.entry+0x94⟩,
       ⟨s.setReg (.low .rsi .W32) (s.regs.get (.low .rbp .W32)), Image.PeerGet.entry+0x96⟩,
       ⟨zeroed (s.setReg (.low .rsi .W32) (s.regs.get (.low .rbp .W32)))
         (.low .rdi .W32) af, Image.PeerGet.entry+0x98⟩] =
      .ok [LookupObservation.decision rxSection .peerGetMaybeZeroDead
        (s.regs.get (.low .rbp .W32) == 0)
        ⟨s.setReg (.low .rsi .W32) (s.regs.get (.low .rbp .W32)), Image.PeerGet.entry+0x96⟩] := by
  simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  rfl

#print axioms dead_wrap_arguments_history
#print axioms dead_wrap_observed
#print axioms live_result_observed

#print axioms xor_mov_history
#print axioms xor_xor_history
#print axioms mov_xor_history
end Binary.PeerGet
