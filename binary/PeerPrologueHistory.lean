import CallHistory
import StackFrame

set_option maxRecDepth 4096
set_option maxHeartbeats 400000

namespace Binary.PeerGet
local instance : Labels := Image.linkedLabels

private theorem u64_sub_sub (a b c : UInt64) : a-b-c = a-(b+c) := by
  apply UInt64.toBitVec_inj.mp
  exact BitVec.sub_sub _ _ _

/-- Exact states after the six register saves. The seventh saved word is
    pushed by the real instrumentation CALL, separately below. -/
def pushedData (s : MachineData) (n : Nat) : MachineData :=
  {s with regs := {s.regs with rsp := s.regs.rsp - UInt64.ofNat (8*n)}, dmem := saveMemory s n}

def copiedData (s : MachineData) : MachineData :=
  {pushedData s 6 with regs := {(pushedData s 6).regs with rbx := s.regs.rdi}}

def prologueStates (s : MachineData) : List MachineState :=
  [⟨pushedData s 1, Image.PeerGet.entry+2⟩,
   ⟨pushedData s 2, Image.PeerGet.entry+4⟩,
   ⟨pushedData s 3, Image.PeerGet.entry+6⟩,
   ⟨pushedData s 4, Image.PeerGet.entry+8⟩,
   ⟨pushedData s 5, Image.PeerGet.entry+9⟩,
   ⟨pushedData s 6, Image.PeerGet.entry+10⟩,
   ⟨copiedData s, Image.PeerGet.entry+13⟩]

private theorem history_cons (fetch : Int64 → Option Decoded) (s next : MachineState)
    (history : List MachineState) (n : Nat) (P : Executed → Prop)
    (first : instructionStep fetch s (fun t => t = next))
    (rest : historySteps fetch n P ⟨next, history ++ [next]⟩) :
    historySteps fetch (n+1) P ⟨s, history⟩ := by
  exact instruction_mono fetch s (fun t => t = next) _ (fun t ht => ht ▸ rest) first

private theorem push0 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec - 8) 8).isSome = true) :
    instructionStep fetch ⟨pushedData s 0, Image.PeerGet.entry+0⟩
      (fun t => t = ⟨pushedData s 1, Image.PeerGet.entry+2⟩) := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+0) = some _ from rfl)
  have defined := saves_preserve_mapped s 0 _ mapped
  obtain ⟨value, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, Reg64s.get, Reg64s.get64, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, pushedData, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem push1 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec - 16) 8).isSome = true) :
    instructionStep fetch ⟨pushedData s 1, Image.PeerGet.entry+2⟩
      (fun t => t = ⟨pushedData s 2, Image.PeerGet.entry+4⟩) := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+2) = some _ from rfl)
  have defined := saves_preserve_mapped s 1 _ mapped
  obtain ⟨value, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, Reg64s.get, Reg64s.get64, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, pushedData, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem push2 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec - 24) 8).isSome = true) :
    instructionStep fetch ⟨pushedData s 2, Image.PeerGet.entry+4⟩
      (fun t => t = ⟨pushedData s 3, Image.PeerGet.entry+6⟩) := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+4) = some _ from rfl)
  have defined := saves_preserve_mapped s 2 _ mapped
  obtain ⟨value, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, Reg64s.get, Reg64s.get64, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, pushedData, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem push3 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec - 32) 8).isSome = true) :
    instructionStep fetch ⟨pushedData s 3, Image.PeerGet.entry+6⟩
      (fun t => t = ⟨pushedData s 4, Image.PeerGet.entry+8⟩) := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+6) = some _ from rfl)
  have defined := saves_preserve_mapped s 3 _ mapped
  obtain ⟨value, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, Reg64s.get, Reg64s.get64, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, pushedData, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem push4 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec - 40) 8).isSome = true) :
    instructionStep fetch ⟨pushedData s 4, Image.PeerGet.entry+8⟩
      (fun t => t = ⟨pushedData s 5, Image.PeerGet.entry+9⟩) := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+8) = some _ from rfl)
  have defined := saves_preserve_mapped s 4 _ mapped
  obtain ⟨value, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, Reg64s.get, Reg64s.get64, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, pushedData, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem push5 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec - 48) 8).isSome = true) :
    instructionStep fetch ⟨pushedData s 5, Image.PeerGet.entry+9⟩
      (fun t => t = ⟨pushedData s 6, Image.PeerGet.entry+10⟩) := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+9) = some _ from rfl)
  have defined := saves_preserve_mapped s 5 _ mapped
  obtain ⟨value, loaded⟩ := Option.isSome_iff_exists.mp defined
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.store, Reg64s.get, Reg64s.get64, Reg64s.set64,
    Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    Width.bytesv, pushedData, BitVec.sub_sub, u64_sub_sub,
    saveMemory, savedWords] at loaded ⊢
  simp_all [Effects.All, BitVec.sub_sub]
  try rfl

private theorem copy_argument (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData) :
    instructionStep fetch ⟨pushedData s 6, Image.PeerGet.entry+10⟩
      (fun t => t = ⟨copiedData s, Image.PeerGet.entry+13⟩) := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+10) = some _ from rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.set, MachineData.setReg, Reg64s.get, Reg64s.get64, Reg64s.set,
    Reg64s.set64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, Effects.All,
    copiedData, pushedData]
  rfl

/-- The exact seven-instruction prefix, retaining every actual successor.
    No endpoint proof is lifted to stand in for these intermediate states. -/
theorem saves_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (history : List MachineState)
    (mapped : ∀ n < 6,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    historySteps fetch 7 (fun t =>
      t.machine = ⟨copiedData s, Image.PeerGet.entry+13⟩ ∧
      t.history = history ++ prologueStates s)
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  have zero : (⟨pushedData s 0, Image.PeerGet.entry+0⟩ : MachineState) = ⟨s, Image.PeerGet.entry⟩ := by
    simp [pushedData, saveMemory]
  rw [← zero]
  apply history_cons fetch _ ⟨pushedData s 1, Image.PeerGet.entry+2⟩
  · exact push0 fetch agree s (mapped 0 (by decide))
  apply history_cons fetch _ ⟨pushedData s 2, Image.PeerGet.entry+4⟩
  · exact push1 fetch agree s (mapped 1 (by decide))
  apply history_cons fetch _ ⟨pushedData s 3, Image.PeerGet.entry+6⟩
  · exact push2 fetch agree s (mapped 2 (by decide))
  apply history_cons fetch _ ⟨pushedData s 4, Image.PeerGet.entry+8⟩
  · exact push3 fetch agree s (mapped 3 (by decide))
  apply history_cons fetch _ ⟨pushedData s 5, Image.PeerGet.entry+9⟩
  · exact push4 fetch agree s (mapped 4 (by decide))
  apply history_cons fetch _ ⟨pushedData s 6, Image.PeerGet.entry+10⟩
  · exact push5 fetch agree s (mapped 5 (by decide))
  apply history_cons fetch _ ⟨copiedData s, Image.PeerGet.entry+13⟩
  · exact copy_argument fetch agree s
  simp [historySteps, prologueStates, List.append_assoc]

/-- There are no source decisions in the register-save prefix. -/
theorem saves_observed (rxSection : Nat) (s : MachineData) :
    observeHistory (LookupObservation.edge rxSection)
      (⟨s, Image.PeerGet.entry⟩ :: prologueStates s) = .ok [] := by
  simp [observeHistory, prologueStates, LookupObservation.edge,
    Image.Lookup.entry, Image.PeerGet.entry]

/-- Actual instrumentation entry after its return-address push. -/
def prologueCalled (s : MachineData) : MachineState :=
  Instrumentation.calledState (copiedData s) (Image.PeerGet.entry+0x12)
    (.ofNat 0xffffffff810f3100)

theorem prologue_called_memory (s : MachineData) :
    (prologueCalled s).data.dmem = saveMemory s 7 := by
  simp only [prologueCalled, Instrumentation.calledState, copiedData, pushedData,
    UInt64.toBitVec_sub, BitVec.sub_sub]
  rfl

/-- All eight prologue instructions, including the actual CALL to KCOV. -/
theorem prologue_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (history : List MachineState)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true) :
    historySteps fetch 8 (fun t => t.machine = prologueCalled s ∧
      t.history = history ++ (prologueStates s ++ [prologueCalled s]))
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  rw [show 8 = 7+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 7 _ _ _ _
    (saves_history fetch agree s history (fun n hn => mapped n (by omega)))
  rintro t ⟨machine, recorded⟩
  have cursor : t = ⟨⟨copiedData s, Image.PeerGet.entry+13⟩, history ++ prologueStates s⟩ := by
    cases t; simp_all
  rw [cursor]
  have stack : ((copiedData s).dmem.loadInt ((copiedData s).regs.rsp.toBitVec-8) 8).isSome = true := by
    have preserved := saves_preserve_mapped s 6 _ (mapped 6 (by decide))
    simp only [copiedData, pushedData, UInt64.toBitVec_sub, BitVec.sub_sub]
    exact preserved
  have call := Instrumentation.call_instruction fetch (Image.PeerGet.entry+13)
    "L_ffffffff810f3100" (agree _ _ (by rfl)) (copiedData s)
    (history ++ prologueStates s) stack
  apply historySteps_mono fetch 1 _ _ _ _ call
  rintro final ⟨machine, recorded⟩
  refine ⟨machine, ?_⟩
  rw [recorded, machine, List.append_assoc]
  rfl

theorem prologue_observed (rxSection : Nat) (s : MachineData) :
    observeHistory (LookupObservation.edge rxSection)
      (⟨s, Image.PeerGet.entry⟩ :: (prologueStates s ++ [prologueCalled s])) = .ok [] := by
  simp [observeHistory, prologueStates, LookupObservation.edge,
    Image.Lookup.entry, Image.PeerGet.entry]

#print axioms prologue_called_memory
#print axioms prologue_history
#print axioms prologue_observed

#print axioms saves_history
#print axioms saves_observed
end Binary.PeerGet
