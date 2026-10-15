import OwnerStore
import PeerClearHistory

namespace Binary.LookupHistory
local instance : Labels := Image.linkedLabels

def resultSaved (s : MachineData) : MachineData :=
  (OwnerWord.stored s).setReg (.low .rbp .W64) s.regs.rax.toBitVec

def resultExit (s : MachineData) (af : Bool) : MachineState :=
  ⟨tested (.low .rax .W64) (resultSaved s) af,
    if s.regs.rax = 0 then Image.Lookup.entry+0x71 else Image.Lookup.entry+0xc5⟩

def resultStates (s : MachineData) (af : Bool) : List MachineState :=
  [⟨OwnerWord.stored s, Image.Lookup.entry+0xbd⟩,
   ⟨resultSaved s, Image.Lookup.entry+0xc0⟩,
   ⟨tested (.low .rax .W64) (resultSaved s) af, Image.Lookup.entry+0xc3⟩,
   resultExit s af]

/-- The saved result is the actual helper return register, including NULL. -/
theorem save_result (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (history : List MachineState) :
    historySteps fetch 1 (fun t =>
      t.machine = ⟨resultSaved s, Image.Lookup.entry+0xc0⟩ ∧
      t.history = history ++ [t.machine])
      ⟨⟨OwnerWord.stored s, Image.Lookup.entry+0xbd⟩, history⟩ := by
  refine instruction_history fetch _ history
    (fun t => t = ⟨resultSaved s, Image.Lookup.entry+0xc0⟩) ?_
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+0xbd) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    MachineData.set, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, resultSaved, OwnerWord.stored]
  rfl

/-- Store through the owner before testing the returned peer. Both the dead
    and live paths retain the store and every actual intermediate state. -/
theorem result_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (peers : Leanux.WG.PeerId → BitVec 64) (s : MachineData) (old : Option Leanux.WG.PeerId)
    (represented : OwnerWord.Field peers s.dmem s.regs.rbx.toBitVec old)
    (history : List MachineState) :
    historySteps fetch 4 (fun t => ∃ af,
      t.machine = resultExit s af ∧ t.history = history ++ resultStates s af)
      ⟨⟨s, Image.Lookup.entry+0xba⟩, history⟩ := by
  rw [show 4 = 1+3 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _
    (OwnerWord.store_history fetch agree peers s old represented history)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨OwnerWord.stored s, Image.Lookup.entry+0xbd⟩,
      history ++ [⟨OwnerWord.stored s, Image.Lookup.entry+0xbd⟩]⟩ := by
    cases t; simp_all
  rw [cursor, show 3 = 1+2 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (save_result fetch agree s _)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨resultSaved s, Image.Lookup.entry+0xc0⟩,
      history ++ [⟨OwnerWord.stored s, Image.Lookup.entry+0xbd⟩,
        ⟨resultSaved s, Image.Lookup.entry+0xc0⟩]⟩ := by
    cases t; simp_all [List.append_assoc]
  rw [cursor]
  have guard := test_self fetch (Image.Lookup.entry+0xc0) .W64 (.low .rax .W64)
    "L_ffffffff813a04e1" 3 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) (resultSaved s)
    (history ++ [⟨OwnerWord.stored s, Image.Lookup.entry+0xbd⟩,
      ⟨resultSaved s, Image.Lookup.entry+0xc0⟩])
  apply historySteps_mono fetch 2 _ _ _ _ guard
  rintro t ⟨af, machine, recorded⟩
  have reg : (resultSaved s).regs.get (.low .rax .W64) = s.regs.rax.toBitVec := by
    simp [resultSaved, OwnerWord.stored, MachineData.setReg, Reg64s.set,
      Reg64s.set64, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take]
  have zero : s.regs.rax.toBitVec = 0#64 ↔ s.regs.rax = 0 := UInt64.toBitVec_inj
  have branch : (if (resultSaved s).regs.get (.low .rax .W64) == 0 then
      label "L_ffffffff813a04e1" else Image.Lookup.entry+0xc0+Int64.ofNat 3+Int64.ofNat 2) =
      (if s.regs.rax = 0 then Image.Lookup.entry+0x71 else Image.Lookup.entry+0xc5) := by
    rw [reg]
    change (if s.regs.rax.toBitVec == 0#64 then _ else _) = _
    by_cases h : s.regs.rax = 0
    · rw [ite_eq_left h, ite_eq_left (by simpa only [beq_iff_eq] using zero.mpr h)]
      rfl
    · rw [ite_eq_right h, ite_eq_right (by simpa only [beq_iff_eq] using (fun hz => h (zero.mp hz)))]
      rfl
  rw [branch] at machine recorded
  refine ⟨af, ?_, ?_⟩
  · exact machine
  · simpa only [resultExit, resultStates,
      show Image.Lookup.entry+0xc0+Int64.ofNat 3 = Image.Lookup.entry+0xc3 from rfl, List.append_assoc,
      List.cons_append, List.nil_append] using recorded

theorem result_observed (rxSection : Nat) (s : MachineData) (af : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      (⟨s, Image.Lookup.entry+0xba⟩ :: resultStates s af) =
      .ok [LookupObservation.decision rxSection .idxPeerAlive
        (decide (s.regs.rax ≠ 0)) (resultExit s af)] := by
  by_cases zero : s.regs.rax = 0
  all_goals simp [observeHistory, resultStates, resultExit, LookupObservation.edge,
    LookupObservation.choice, Image.Lookup.entry, Image.PeerGet.entry, zero]
  all_goals rfl

/-- The owner word is already updated at every successor of this region;
    no positivity or non-NULL hypothesis is involved. -/
theorem resultStates_memory (s : MachineData) (af : Bool) (q : MachineState)
    (member : q ∈ resultStates s af) : q.data.dmem = (OwnerWord.stored s).dmem := by
  simp only [resultStates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> rfl

def outputStored (s : MachineData) : MachineData :=
  {s with dmem := s.dmem.storeInt s.regs.r13.toBitVec 8 s.regs.rbp.toBitVec.toInt}

/-- The successful path writes the out-parameter after its PC callback.
    Only mapped storage is needed here; alias restrictions belong to the
    relation for the surrounding call, not the instruction semantics. -/
theorem output_store (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : (s.dmem.loadInt s.regs.r13.toBitVec 8).isSome = true)
    (history : List MachineState) :
    historySteps fetch 1 (fun t => t.machine = ⟨outputStored s, Image.Lookup.entry+0xce⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, Image.Lookup.entry+0xca⟩, history⟩ := by
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp mapped
  refine instruction_history fetch _ history
    (fun t => t = ⟨outputStored s, Image.Lookup.entry+0xce⟩) ?_
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+0xca) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, AddrExpr.interp, ConstExpr.interp,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take,
    Effects.All, BitVec.toAddressSize, BitVec.signed, BitVec.ofInt_toInt,
    outputStored] at loaded ⊢
  rw [loaded]
  simp [Effects.All]
  rfl

theorem output_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : (s.dmem.loadInt s.regs.r13.toBitVec 8).isSome = true)
    (history : List MachineState) :
    historySteps fetch 2 (fun t => t.machine = ⟨outputStored s, Image.Lookup.entry+0x73⟩ ∧
      t.history = history ++ [⟨outputStored s, Image.Lookup.entry+0xce⟩, t.machine])
      ⟨⟨s, Image.Lookup.entry+0xca⟩, history⟩ := by
  rw [show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _ (output_store fetch agree s mapped history)
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨outputStored s, Image.Lookup.entry+0xce⟩,
      history ++ [⟨outputStored s, Image.Lookup.entry+0xce⟩]⟩ := by
    cases t; simp_all
  rw [cursor]
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+0xce) = some _ from rfl)
  simp only [historySteps, historyStep, instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp, Effects.All,
    Image.Lookup.entry, List.append_assoc]
  rfl

theorem output_observed (rxSection : Nat) (s : MachineData) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.Lookup.entry+0xca⟩, ⟨outputStored s, Image.Lookup.entry+0xce⟩,
        ⟨outputStored s, Image.Lookup.entry+0x73⟩] = .ok [] := by
  simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]

theorem output_value (s : MachineData) :
    (outputStored s).dmem.loadInt s.regs.r13.toBitVec 8 = some (s.regs.rbp.toNat : Int) :=
  load64_store _ _ _

theorem output_frame (s : MachineData) :
    EqualOutside (InRange s.regs.r13.toBitVec 8) s.dmem (outputStored s).dmem :=
  storeInt_frame _ _ _ _

#print axioms result_history
#print axioms result_observed
#print axioms resultStates_memory
#print axioms output_history
#print axioms output_observed
#print axioms output_value
#print axioms output_frame
end Binary.LookupHistory
