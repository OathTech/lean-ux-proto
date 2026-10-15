import LookupLoads

namespace Binary.LookupHistory
local instance : Labels := Image.linkedLabels

def typeBits (s : MachineData) (kind : UInt32) : BitVec 32 :=
  s.regs.get (.low .r14 .W32) &&& kind.toBitVec

def typeMasked (s : MachineData) (kind : UInt32) (af : Bool) : MachineData :=
  {s with status := StatusFlags.from_result (typeBits s kind) {cf := false, af, of := false}}
    |>.setReg (.low .r14 .W32) (typeBits s kind)

def argumentZero (s : MachineData) (af : Bool) : MachineData :=
  {s with status := StatusFlags.from_result (0#32) {cf := false, af, of := false}}
    |>.setReg (.low .rdi .W32) 0

def typeArguments (s : MachineData) (kind : UInt32) (af : Bool) : MachineData :=
  (argumentZero (typeMasked s kind false) af).setReg (.low .rsi .W32) (typeBits s kind)

/-- The AND's undefined AF is quantified and retained in the actual state. -/
theorem type_and (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (kind : UInt32) (history : List MachineState)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec+24) 4 = some kind.toNat) :
    historySteps fetch 1 (fun t => ∃ af,
      t.machine = ⟨typeMasked s kind af, Image.Lookup.entry+0x9e⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨s, Image.Lookup.entry+0x9a⟩, history⟩ := by
  have here := agree (Image.Lookup.entry+0x9a)
    ⟨.regular .W64 .W32 (.and (.reg (.low .r14 .W32))
      (.regOrMem (.mem {base := some (.reg .rbx), idx := none, disp := .int64 24}))), 4⟩ (by rfl)
  simp only [historySteps, historyStep, instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, AddrExpr.interp, Reg64s.get64,
    ConstExpr.interp, BitVec.toAddressSize, BitVec.signed, BitVec.take,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat, Effects.All,
    typeMasked, typeBits, Image.Lookup.entry] at field ⊢
  rw [field]
  simp [Effects.All, BitVec.ofInt_ofNat]

theorem zero_argument (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 1 (fun t => ∃ af,
      t.machine = ⟨argumentZero s af, Image.Lookup.entry+0xa0⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨s, Image.Lookup.entry+0x9e⟩, history⟩ := by
  have here := agree (Image.Lookup.entry+0x9e)
    ⟨.regular .W64 .W32 (.xor (.reg (.low .rdi .W32)) (.regOrMem (.reg (.low .rdi .W32)))), 2⟩ (by rfl)
  simp only [historySteps, historyStep, instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.set, Effects.All, argumentZero, Image.Lookup.entry]

/-- XOR discards the AND's flags, but not its register or memory changes. -/
theorem argumentZero_masked (s : MachineData) (kind : UInt32) (af₁ af₂ : Bool) :
    argumentZero (typeMasked s kind af₁) af₂ =
    argumentZero (typeMasked s kind false) af₂ := rfl

theorem type_register (s : MachineData) (kind : UInt32) (af₁ af₂ : Bool) :
    (argumentZero (typeMasked s kind af₁) af₂).regs.get (.low .r14 .W32) = typeBits s kind := by
  simp [argumentZero, typeMasked, MachineData.setReg, Reg64s.set, Reg64s.set64,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

theorem type_arguments (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (kind : UInt32) (history : List MachineState)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec+24) 4 = some kind.toNat) :
    historySteps fetch 3 (fun t => ∃ af₁ af₂,
      t.machine = ⟨typeArguments s kind af₂, Image.Lookup.entry+0xa3⟩ ∧
      t.history = history ++ [⟨typeMasked s kind af₁, Image.Lookup.entry+0x9e⟩,
        ⟨argumentZero (typeMasked s kind af₁) af₂, Image.Lookup.entry+0xa0⟩,
        ⟨typeArguments s kind af₂, Image.Lookup.entry+0xa3⟩])
      ⟨⟨s, Image.Lookup.entry+0x9a⟩, history⟩ := by
  rw [show 3 = 1+2 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (type_and fetch agree s kind history field)
  rintro t ⟨af₁, machine, recorded⟩
  have state : t = ⟨⟨typeMasked s kind af₁, Image.Lookup.entry+0x9e⟩,
      history ++ [⟨typeMasked s kind af₁, Image.Lookup.entry+0x9e⟩]⟩ := by
    cases t; simp_all
  rw [state, show 2 = 1+1 from rfl, historySteps_add]
  have second := zero_argument fetch agree (typeMasked s kind af₁)
    (history ++ [⟨typeMasked s kind af₁, Image.Lookup.entry+0x9e⟩])
  apply historySteps_mono fetch 1 _ _ _ _ second
  rintro t ⟨af₂, machine, recorded⟩
  have state : t = ⟨⟨argumentZero (typeMasked s kind af₁) af₂, Image.Lookup.entry+0xa0⟩,
      history ++ [⟨typeMasked s kind af₁, Image.Lookup.entry+0x9e⟩,
        ⟨argumentZero (typeMasked s kind af₁) af₂, Image.Lookup.entry+0xa0⟩]⟩ := by
    cases t; simp_all [List.append_assoc]
  rw [state]
  have third := mov32_history fetch (Image.Lookup.entry+0xa0) (.low .rsi .W32) (.low .r14 .W32)
      3 (by decide) (agree _ _ (by rfl)) (argumentZero (typeMasked s kind af₁) af₂)
      (history ++ [⟨typeMasked s kind af₁, Image.Lookup.entry+0x9e⟩,
        ⟨argumentZero (typeMasked s kind af₁) af₂, Image.Lookup.entry+0xa0⟩])
  apply historySteps_mono fetch 1 _ _ _ _ third
  rintro t ⟨machine, recorded⟩
  have final : t.machine = ⟨typeArguments s kind af₂, Image.Lookup.entry+0xa3⟩ := by
    simpa only [type_register, argumentZero_masked, typeArguments,
      show Image.Lookup.entry+0xa0+Int64.ofNat 3 = Image.Lookup.entry+0xa3 from rfl] using machine
  exact ⟨af₁, af₂, final, by
    simpa only [final, List.append_assoc, List.cons_append, List.nil_append] using recorded⟩

/-- The branch is exactly source kind membership for every list of kinds.
    The mask can be zero; a wrong-kind first index match is not skipped. -/
theorem type_source (s : MachineData) (kind : Leanux.WG.IndexKind)
    (kinds : List Leanux.WG.IndexKind)
    (mask : KindMask (s.regs.get (.low .r14 .W32)) kinds) :
    decide (typeBits s (.ofBitVec (kindWord kind)) ≠ 0) = kinds.contains kind := by
  unfold typeBits
  exact mask kind

#print axioms type_source

#print axioms type_and
#print axioms zero_argument
#print axioms type_register
#print axioms type_arguments
end Binary.LookupHistory
