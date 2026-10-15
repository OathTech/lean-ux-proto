import LookupStackFrame
import CallHistory

set_option maxRecDepth 4096
set_option maxHeartbeats 400000
namespace Binary.Lookup
local instance : Labels := Image.linkedLabels

private theorem u64_sub_sub (a b c : UInt64) : a-b-c = a-(b+c) := by
  apply UInt64.toBitVec_inj.mp
  exact BitVec.sub_sub _ _ _

def savedCount : Nat → Nat
  | 0 => 0
  | 1 | 2 => 1
  | 3 | 4 => 2
  | 5 | 6 => 3
  | 7 => 4
  | _ => 5

/-- Interleaved argument copies happen only after their old register was
    saved. The memory stack therefore contains the original ABI values. -/
def prologueData (s : MachineData) (n : Nat) : MachineData :=
  {s with dmem := saveMemory s (savedCount n), regs := {s.regs with
    rsp := s.regs.rsp - UInt64.ofNat (8 * savedCount n)
    r14 := if 2 ≤ n then .ofNat (s.regs.get (.low .rsi .W32)).toNat else s.regs.r14
    r13 := if 4 ≤ n then s.regs.rcx else s.regs.r13
    r12 := if 6 ≤ n then .ofNat (s.regs.get (.low .rdx .W32)).toNat else s.regs.r12
    rbx := if 9 ≤ n then s.regs.rdi else s.regs.rbx}}

def prologueStates (s : MachineData) : List MachineState :=
  [⟨prologueData s 1, Image.Lookup.entry+2⟩,
   ⟨prologueData s 2, Image.Lookup.entry+5⟩,
   ⟨prologueData s 3, Image.Lookup.entry+7⟩,
   ⟨prologueData s 4, Image.Lookup.entry+10⟩,
   ⟨prologueData s 5, Image.Lookup.entry+12⟩,
   ⟨prologueData s 6, Image.Lookup.entry+15⟩,
   ⟨prologueData s 7, Image.Lookup.entry+16⟩,
   ⟨prologueData s 8, Image.Lookup.entry+17⟩,
   ⟨prologueData s 9, Image.Lookup.entry+20⟩]

private theorem history_cons (fetch : Int64 → Option Decoded) (s next : MachineState)
    (history : List MachineState) (n : Nat) (P : Executed → Prop)
    (first : instructionStep fetch s (fun t => t = next))
    (rest : historySteps fetch n P ⟨next, history ++ [next]⟩) :
    historySteps fetch (n+1) P ⟨s, history⟩ := by
  exact instruction_mono fetch s (fun t => t = next) _ (fun t ht => ht ▸ rest) first

private theorem instruction0 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 0, Image.Lookup.entry+0⟩
      (fun t => t = ⟨prologueData s 1, Image.Lookup.entry+2⟩) := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+0) = some _ from rfl)
  have defined := saves_preserve_mapped s 0 _ (mapped 0 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem instruction1 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 1, Image.Lookup.entry+2⟩
      (fun t => t = ⟨prologueData s 2, Image.Lookup.entry+5⟩) := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+2) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords]
  refine ⟨?_, rfl⟩
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp

private theorem instruction2 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 2, Image.Lookup.entry+5⟩
      (fun t => t = ⟨prologueData s 3, Image.Lookup.entry+7⟩) := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+5) = some _ from rfl)
  have defined := saves_preserve_mapped s 1 _ (mapped 1 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem instruction3 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 3, Image.Lookup.entry+7⟩
      (fun t => t = ⟨prologueData s 4, Image.Lookup.entry+10⟩) := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+7) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords]
  try rfl

private theorem instruction4 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 4, Image.Lookup.entry+10⟩
      (fun t => t = ⟨prologueData s 5, Image.Lookup.entry+12⟩) := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+10) = some _ from rfl)
  have defined := saves_preserve_mapped s 2 _ (mapped 2 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem instruction5 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 5, Image.Lookup.entry+12⟩
      (fun t => t = ⟨prologueData s 6, Image.Lookup.entry+15⟩) := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+12) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords]
  refine ⟨?_, rfl⟩
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_toNat_eq
  simp

private theorem instruction6 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 6, Image.Lookup.entry+15⟩
      (fun t => t = ⟨prologueData s 7, Image.Lookup.entry+16⟩) := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+15) = some _ from rfl)
  have defined := saves_preserve_mapped s 3 _ (mapped 3 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem instruction7 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 7, Image.Lookup.entry+16⟩
      (fun t => t = ⟨prologueData s 8, Image.Lookup.entry+17⟩) := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+16) = some _ from rfl)
  have defined := saves_preserve_mapped s 4 _ (mapped 4 (by decide))
  obtain ⟨word, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem instruction8 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    instructionStep fetch ⟨prologueData s 8, Image.Lookup.entry+17⟩
      (fun t => t = ⟨prologueData s 9, Image.Lookup.entry+20⟩) := by
  have here := agree _ _ (show Image.fetch (Image.Lookup.entry+17) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, MachineData.set, MachineData.setReg,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, prologueData, savedCount, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords]
  try rfl

/-- Nine actual prologue successors, before the instrumentation CALL. -/
theorem saves_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (history : List MachineState)
    (mapped : ∀ n < 5, (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    historySteps fetch 9 (fun t => t.machine = ⟨prologueData s 9, Image.Lookup.entry+20⟩ ∧
      t.history = history ++ prologueStates s) ⟨⟨s, Image.Lookup.entry⟩, history⟩ := by
  have initial : (⟨prologueData s 0, Image.Lookup.entry+0⟩ : MachineState) = ⟨s, Image.Lookup.entry⟩ := by
    simp [prologueData, savedCount, saveMemory]
  rw [← initial]
  apply history_cons fetch _ ⟨prologueData s 1, Image.Lookup.entry+2⟩
  · exact instruction0 fetch agree s mapped
  apply history_cons fetch _ ⟨prologueData s 2, Image.Lookup.entry+5⟩
  · exact instruction1 fetch agree s mapped
  apply history_cons fetch _ ⟨prologueData s 3, Image.Lookup.entry+7⟩
  · exact instruction2 fetch agree s mapped
  apply history_cons fetch _ ⟨prologueData s 4, Image.Lookup.entry+10⟩
  · exact instruction3 fetch agree s mapped
  apply history_cons fetch _ ⟨prologueData s 5, Image.Lookup.entry+12⟩
  · exact instruction4 fetch agree s mapped
  apply history_cons fetch _ ⟨prologueData s 6, Image.Lookup.entry+15⟩
  · exact instruction5 fetch agree s mapped
  apply history_cons fetch _ ⟨prologueData s 7, Image.Lookup.entry+16⟩
  · exact instruction6 fetch agree s mapped
  apply history_cons fetch _ ⟨prologueData s 8, Image.Lookup.entry+17⟩
  · exact instruction7 fetch agree s mapped
  apply history_cons fetch _ ⟨prologueData s 9, Image.Lookup.entry+20⟩
  · exact instruction8 fetch agree s mapped
  simp [historySteps, prologueStates, List.append_assoc]

/-- No anchored event is emitted by the save/copy prefix. -/
theorem saves_observed (rxSection : Nat) (s : MachineData) :
    observeHistory (LookupObservation.edge rxSection)
      (⟨s, Image.Lookup.entry⟩ :: prologueStates s) = .ok [] := by
  simp [observeHistory, prologueStates, LookupObservation.edge,
    Image.Lookup.entry, Image.PeerGet.entry]

def prologueCalled (s : MachineData) : MachineState :=
  Instrumentation.calledState (prologueData s 9) (Image.Lookup.entry+0x19)
    (.ofNat 0xffffffff810f3100)

theorem prologue_called_memory (s : MachineData) :
    (prologueCalled s).data.dmem = saveMemory s 6 := by
  simp only [prologueCalled, Instrumentation.calledState, prologueData, savedCount,
    UInt64.toBitVec_sub, BitVec.sub_sub]
  rfl

/-- All ten actual entry instructions, including the sixth stack write by
    CALL. The original return word sits immediately above five register saves. -/
theorem prologue_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (history : List MachineState)
    (mapped : ∀ n < 6,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    historySteps fetch 10 (fun t => t.machine = prologueCalled s ∧
      t.history = history ++ (prologueStates s ++ [prologueCalled s]))
      ⟨⟨s, Image.Lookup.entry⟩, history⟩ := by
  rw [show 10 = 9+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 9 _ _ _ _
    (saves_history fetch agree s history (fun n hn => mapped n (by omega)))
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨prologueData s 9, Image.Lookup.entry+20⟩,
      history ++ prologueStates s⟩ := by
    cases t; simp_all
  rw [cursor]
  have stack : ((prologueData s 9).dmem.loadInt
      ((prologueData s 9).regs.rsp.toBitVec-8) 8).isSome = true := by
    have preserved := saves_preserve_mapped s 5 _ (mapped 5 (by decide))
    simp only [prologueData, savedCount, UInt64.toBitVec_sub, BitVec.sub_sub]
    exact preserved
  have call := Instrumentation.call_instruction fetch (Image.Lookup.entry+20)
    "L_ffffffff810f3100" (agree _ _ (by rfl)) (prologueData s 9)
    (history ++ prologueStates s) stack
  apply historySteps_mono fetch 1 _ _ _ _ call
  rintro final ⟨machine, recorded⟩
  refine ⟨machine, ?_⟩
  rw [recorded, machine, List.append_assoc]
  rfl

theorem prologue_observed (rxSection : Nat) (s : MachineData) :
    observeHistory (LookupObservation.edge rxSection)
      (⟨s, Image.Lookup.entry⟩ :: (prologueStates s ++ [prologueCalled s])) = .ok [] := by
  simp [observeHistory, prologueStates, LookupObservation.edge,
    Image.Lookup.entry, Image.PeerGet.entry]

theorem prologue_frames (s : MachineData) (q : MachineState)
    (member : q ∈ prologueStates s ++ [prologueCalled s]) :
    EqualOutside (InRange (s.regs.rsp.toBitVec-48) 48) s.dmem q.data.dmem := by
  simp only [prologueStates, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact saveMemory_frame s 1 (by decide)
  · exact saveMemory_frame s 1 (by decide)
  · exact saveMemory_frame s 2 (by decide)
  · exact saveMemory_frame s 2 (by decide)
  · exact saveMemory_frame s 3 (by decide)
  · exact saveMemory_frame s 3 (by decide)
  · exact saveMemory_frame s 4 (by decide)
  · exact saveMemory_frame s 5 (by decide)
  · exact saveMemory_frame s 5 (by decide)
  · rw [prologue_called_memory]
    exact saveMemory_frame s 6 (by decide)

#print axioms prologue_called_memory
#print axioms prologue_history
#print axioms prologue_observed
#print axioms prologue_frames
#print axioms saves_history
#print axioms saves_observed
end Binary.Lookup
