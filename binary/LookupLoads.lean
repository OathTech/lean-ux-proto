import BucketLoop

set_option maxHeartbeats 1000000
namespace Binary.LookupHistory
local instance : Labels := Image.linkedLabels

/-- A MOV is retained as one real successor, without discarding any cut. -/
theorem mov32_history (fetch : Int64 → Option Decoded) (pc : Int64)
    (dst src : Reg .W32) (size : Nat) (positive : 0 < size)
    (here : fetch pc = some ⟨.regular .W64 .W32 (.mov (.reg dst) (.regOrMem (.reg src))), size⟩)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨s.setReg dst (s.regs.get src), pc + .ofNat size⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, pc⟩, history⟩ := by
  refine instruction_history fetch ⟨s, pc⟩ history
    (fun t => t = ⟨s.setReg dst (s.regs.get src), pc + .ofNat size⟩) ?_
  simp only [instructionStep, here]
  exact ⟨positive, by simp [Instr.interp, Operation.interp, Operand.interp,
    RegOrMem.interp, MachineData.set, Effects.All]⟩

def indexLoaded (s : MachineData) (index : UInt32) : MachineData :=
  s.setReg (.low .rbp .W32) index.toBitVec
def indexArgs1 (s : MachineData) (index : UInt32) : MachineData :=
  (indexLoaded s index).setReg (.low .rsi .W32) (s.regs.get (.low .r12 .W32))
def indexArgs2 (s : MachineData) (index : UInt32) : MachineData :=
  (indexArgs1 s index).setReg (.low .rdi .W32) index.toBitVec

theorem index_word (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (index : UInt32) (history : List MachineState)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec + 28) 4 = some index.toNat) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨indexLoaded s index, Image.Lookup.entry + 0x4f⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨s, Image.Lookup.entry + 0x4c⟩, history⟩ := by
  have here := agree (Image.Lookup.entry + 0x4c)
    ⟨.regular .W64 .W32 (.mov (.reg (.low .rbp .W32))
      (.regOrMem (.mem {base := some (.reg .rbx), idx := none, disp := .int64 28}))), 3⟩ (by rfl)
  refine instruction_history fetch ⟨s, Image.Lookup.entry + 0x4c⟩ history
    (fun t => t = ⟨indexLoaded s index, Image.Lookup.entry + 0x4f⟩) ?_
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, AddrExpr.interp, Reg64s.get64,
    ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    Effects.All, indexLoaded, BitVec.take, Image.Lookup.entry] at field ⊢
  rw [field]
  simp [Effects.All]

/-- Exact states at all three MOV successors, including the comparison-call
    correspondence point at +0x54. -/
theorem index_arguments (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (index : UInt32) (history : List MachineState)
    (field : s.dmem.loadInt (s.regs.rbx.toBitVec + 28) 4 = some index.toNat) :
    historySteps fetch 3 (fun t =>
      t.machine = ⟨indexArgs2 s index, Image.Lookup.entry + 0x54⟩ ∧
      t.history = history ++ [⟨indexLoaded s index, Image.Lookup.entry + 0x4f⟩,
        ⟨indexArgs1 s index, Image.Lookup.entry + 0x52⟩,
        ⟨indexArgs2 s index, Image.Lookup.entry + 0x54⟩])
      ⟨⟨s, Image.Lookup.entry + 0x4c⟩, history⟩ := by
  rw [show 3 = 1+2 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (index_word fetch agree s index history field)
  rintro t ⟨machine, recorded⟩
  have state : t = ⟨⟨indexLoaded s index, Image.Lookup.entry + 0x4f⟩,
      history ++ [⟨indexLoaded s index, Image.Lookup.entry + 0x4f⟩]⟩ := by
    cases t; simp_all
  rw [state, show 2 = 1+1 from rfl, historySteps_add]
  have second := mov32_history fetch (Image.Lookup.entry + 0x4f)
    (.low .rsi .W32) (.low .r12 .W32) 3 (by decide) (agree _ _ (by rfl)) (indexLoaded s index)
    (history ++ [⟨indexLoaded s index, Image.Lookup.entry + 0x4f⟩])
  apply historySteps_mono fetch 1 _ _ _ _ second
  rintro t ⟨machine, recorded⟩
  have machine1 : t.machine = ⟨indexArgs1 s index, Image.Lookup.entry + 0x52⟩ := by
    exact machine
  have state : t = ⟨⟨indexArgs1 s index, Image.Lookup.entry + 0x52⟩,
      history ++ [⟨indexLoaded s index, Image.Lookup.entry + 0x4f⟩,
        ⟨indexArgs1 s index, Image.Lookup.entry + 0x52⟩]⟩ := by
    cases t; simp_all [List.append_assoc]
  rw [state]
  have third := mov32_history fetch (Image.Lookup.entry + 0x52)
    (.low .rdi .W32) (.low .rbp .W32) 2 (by decide) (agree _ _ (by rfl)) (indexArgs1 s index)
    (history ++ [⟨indexLoaded s index, Image.Lookup.entry + 0x4f⟩,
      ⟨indexArgs1 s index, Image.Lookup.entry + 0x52⟩])
  apply historySteps_mono fetch 1 _ _ _ _ third
  rintro t ⟨machine, recorded⟩
  have read : (indexArgs1 s index).regs.get (.low .rbp .W32) = index.toBitVec := by
    simp [indexArgs1, indexLoaded, MachineData.setReg, Reg64s.set, Reg64s.set64,
      Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
    rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
    simp
  have final : t.machine = ⟨indexArgs2 s index, Image.Lookup.entry + 0x54⟩ := by
    simpa only [read, indexArgs2,
      show Image.Lookup.entry + 0x52 + Int64.ofNat 2 = Image.Lookup.entry + 0x54 from rfl] using machine
  exact ⟨final, by simpa only [final, List.append_assoc, List.cons_append, List.nil_append] using recorded⟩

def containerData (s : MachineData) : MachineData :=
  let a := s.regs.get (.low .rbx .W64)
  let b : BitVec 64 := 8
  let v := a-b
  {s with status := StatusFlags.from_result v {
    cf := v.unsigned != a.unsigned-b.unsigned
    af := (v.take 4).unsigned != (a.take 4).unsigned-(b.take 4).unsigned
    of := v.signed != a.signed-b.signed }} |>.setReg (.low .rbx .W64) v

/-- container_of stops at the actual callback-call cut, before the CALL. -/
theorem container_sub (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨containerData s, Image.Lookup.entry + 0x3d⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨s, Image.Lookup.entry + 0x39⟩, history⟩ := by
  have here := agree (Image.Lookup.entry + 0x39)
    ⟨.regular .W64 .W64 (.sub (.reg (.low .rbx .W64)) (.imm (.int64 8))), 4⟩ (by rfl)
  refine instruction_history fetch ⟨s, Image.Lookup.entry + 0x39⟩ history
    (fun t => t = ⟨containerData s, Image.Lookup.entry + 0x3d⟩) ?_
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.set, ConstExpr.interp, Effects.All, containerData, Image.Lookup.entry]

theorem container_sub_shape (s : MachineData) :
    (containerData s).dmem = s.dmem ∧
    (containerData s).regs = {s.regs with rbx := s.regs.rbx-8} := by
  simp [containerData, MachineData.setReg, Reg64s.set, Reg64s.set64,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]

theorem index_arguments_observation (rxSection : Nat) (s : MachineData) (index : UInt32) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.Lookup.entry+0x4c⟩,
       ⟨indexLoaded s index, Image.Lookup.entry+0x4f⟩,
       ⟨indexArgs1 s index, Image.Lookup.entry+0x52⟩,
       ⟨indexArgs2 s index, Image.Lookup.entry+0x54⟩] = .ok [] := by
  simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]

def typeExit (s : MachineData) (af : Bool) : MachineState :=
  ⟨tested (.low .r14 .W32) s af,
    if s.regs.get (.low .r14 .W32) == 0 then Image.Lookup.entry+0x71 else Image.Lookup.entry+0xad⟩

/-- The terminal kind edge includes the compiler-merged found decision. -/
theorem type_guard_observation (rxSection : Nat) (s : MachineData) (af : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.Lookup.entry+0xa8⟩,
       ⟨tested (.low .r14 .W32) s af, Image.Lookup.entry+0xab⟩, typeExit s af] =
    .ok [LookupObservation.decision rxSection .idxTypeMatch
        (decide (s.regs.get (.low .r14 .W32) ≠ 0)) (typeExit s af),
      LookupObservation.decision rxSection .idxFound
        (decide (s.regs.get (.low .r14 .W32) ≠ 0)) (typeExit s af)] := by
  by_cases zero : s.regs.get (.low .r14 .W32) = 0#32
  all_goals simp [observeHistory, LookupObservation.edge, LookupObservation.choice,
    typeExit, Image.Lookup.entry, Image.PeerGet.entry, zero]
  all_goals rfl

/-- A represented u32 index has exactly its source Nat value. This derives
    the comparison decision from the physical register equation and the
    representation bound, rather than assuming a matching decision. -/
theorem index_source (s : MachineData) (entryIndex query : Nat)
    (entryBound : entryIndex < 2^32) (queryBound : query < 2^32)
    (loaded : s.regs.get (.low .rbp .W32) = BitVec.ofNat 32 entryIndex)
    (argument : s.regs.get (.low .r12 .W32) = BitVec.ofNat 32 query) :
    indexHit s = (entryIndex == query) := by
  simp only [indexHit, loaded, argument, BitVec.toNat_ofNat, Nat.mod_eq_of_lt entryBound,
    Nat.mod_eq_of_lt queryBound]

#print axioms index_source

#print axioms container_sub
#print axioms container_sub_shape
#print axioms index_arguments_observation
#print axioms type_guard_observation

#print axioms mov32_history
#print axioms index_word
#print axioms index_arguments
end Binary.LookupHistory
