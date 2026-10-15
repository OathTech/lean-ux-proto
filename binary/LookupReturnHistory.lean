import TrustBase
import HistoryRegions

set_option maxHeartbeats 400000
set_option maxRecDepth 16384

namespace Binary.LookupReturn
local instance : Labels := Image.linkedLabels

/-- The actual register file after each epilogue instruction, including
    the return. Memory and flags are unchanged. -/
def restoreData (s : MachineData) (bx bp r12 r13 r14 : UInt64) (n : Nat) : MachineData :=
  {s with regs := {s.regs with
    rax := s.regs.rbx
    rbx := if 1 ≤ n then bx else s.regs.rbx
    rbp := if 2 ≤ n then bp else s.regs.rbp
    r12 := if 3 ≤ n then r12 else s.regs.r12
    r13 := if 4 ≤ n then r13 else s.regs.r13
    r14 := if 5 ≤ n then r14 else s.regs.r14
    rsp := s.regs.rsp + UInt64.ofNat (8 * min n 6)}}

def restoreStates (s : MachineData) (bx bp r12 r13 r14 ra : UInt64) : List MachineState :=
  [⟨restoreData s bx bp r12 r13 r14 0, Image.Lookup.entry+0x8c⟩,
   ⟨restoreData s bx bp r12 r13 r14 1, Image.Lookup.entry+0x8d⟩,
   ⟨restoreData s bx bp r12 r13 r14 2, Image.Lookup.entry+0x8e⟩,
   ⟨restoreData s bx bp r12 r13 r14 3, Image.Lookup.entry+0x90⟩,
   ⟨restoreData s bx bp r12 r13 r14 4, Image.Lookup.entry+0x92⟩,
   ⟨restoreData s bx bp r12 r13 r14 5, Image.Lookup.entry+0x94⟩,
   ⟨restoreData s bx bp r12 r13 r14 6, .ofBitVec ra.toBitVec⟩]

private theorem history_cons (fetch : Int64 → Option Decoded) (s next : MachineState)
    (history : List MachineState) (n : Nat) (P : Executed → Prop)
    (first : instructionStep fetch s (fun t => t = next))
    (rest : historySteps fetch n P ⟨next, history ++ [next]⟩) :
    historySteps fetch (n+1) P ⟨s, history⟩ := by
  exact instruction_mono fetch s (fun t => t = next) _ (fun t ht => ht ▸ rest) first

private theorem return_instruction0 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨s, Image.Lookup.entry+0x89⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 0, Image.Lookup.entry+0x8c⟩) := by
  have f0 := agree _ _ (show Image.fetch (Image.Lookup.entry+0x89) = some _ from rfl)
  simp only [instructionStep, f0]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, restoreData] <;> try rfl

private theorem return_instruction1 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 0, Image.Lookup.entry+0x8c⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 1, Image.Lookup.entry+0x8d⟩) := by
  have f1 := agree _ _ (show Image.fetch (Image.Lookup.entry+0x8c) = some _ from rfl)
  simp only [instructionStep, f1]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, restoreData] <;> try rfl

private theorem return_instruction2 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 1, Image.Lookup.entry+0x8d⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 2, Image.Lookup.entry+0x8e⟩) := by
  have f2 := agree _ _ (show Image.fetch (Image.Lookup.entry+0x8d) = some _ from rfl)
  simp only [instructionStep, f2]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, restoreData] <;> try rfl
  try rw [h1]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]

private theorem return_instruction3 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 2, Image.Lookup.entry+0x8e⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 3, Image.Lookup.entry+0x90⟩) := by
  have f3 := agree _ _ (show Image.fetch (Image.Lookup.entry+0x8e) = some _ from rfl)
  simp only [instructionStep, f3]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, restoreData] <;> try rfl
  try rw [h2]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]

private theorem return_instruction4 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 3, Image.Lookup.entry+0x90⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 4, Image.Lookup.entry+0x92⟩) := by
  have f4 := agree _ _ (show Image.fetch (Image.Lookup.entry+0x90) = some _ from rfl)
  simp only [instructionStep, f4]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, restoreData] <;> try rfl
  try rw [h3]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]

private theorem return_instruction5 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 4, Image.Lookup.entry+0x92⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 5, Image.Lookup.entry+0x94⟩) := by
  have f5 := agree _ _ (show Image.fetch (Image.Lookup.entry+0x92) = some _ from rfl)
  simp only [instructionStep, f5]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, restoreData] <;> try rfl
  try rw [h4]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]

private theorem return_instruction6 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 5, Image.Lookup.entry+0x94⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 6, .ofBitVec ra.toBitVec⟩) := by
  have f7 := agree _ _ (show Image.fetch (Image.Lookup.entry+0x94) = some _ from rfl)
  simp only [instructionStep, f7]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, restoreData] <;> try rfl
  try rw [h5]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]
  all_goals apply Int64.toBitVec_inj.mp
  all_goals simp [Image.Lookup.entry]

theorem epilogue_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (ra.toNat : Int)) :
    historySteps fetch 7 (fun t =>
      t.machine = ⟨restoreData s bx bp r12 r13 r14 6, .ofBitVec ra.toBitVec⟩ ∧
      t.history = history ++ restoreStates s bx bp r12 r13 r14 ra)
      ⟨⟨s, Image.Lookup.entry+0x89⟩, history⟩ := by
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 0, Image.Lookup.entry+0x8c⟩
  · exact return_instruction0 fetch agree s history bx bp r12 r13 r14 ra h0 h1 h2 h3 h4 h5
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 1, Image.Lookup.entry+0x8d⟩
  · exact return_instruction1 fetch agree s history bx bp r12 r13 r14 ra h0 h1 h2 h3 h4 h5
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 2, Image.Lookup.entry+0x8e⟩
  · exact return_instruction2 fetch agree s history bx bp r12 r13 r14 ra h0 h1 h2 h3 h4 h5
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 3, Image.Lookup.entry+0x90⟩
  · exact return_instruction3 fetch agree s history bx bp r12 r13 r14 ra h0 h1 h2 h3 h4 h5
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 4, Image.Lookup.entry+0x92⟩
  · exact return_instruction4 fetch agree s history bx bp r12 r13 r14 ra h0 h1 h2 h3 h4 h5
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 5, Image.Lookup.entry+0x94⟩
  · exact return_instruction5 fetch agree s history bx bp r12 r13 r14 ra h0 h1 h2 h3 h4 h5
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 6, .ofBitVec ra.toBitVec⟩
  · exact return_instruction6 fetch agree s history bx bp r12 r13 r14 ra h0 h1 h2 h3 h4 h5
  simp [historySteps, restoreStates, List.append_assoc]


/-- Every actual epilogue successor preserves all memory, including the
    owner peer word and the complete physical World footprint. -/
theorem restoreStates_memory (s : MachineData) (bx bp r12 r13 r14 ra : UInt64)
    (t : MachineState) (member : t ∈ restoreStates s bx bp r12 r13 r14 ra) :
    t.data.dmem = s.dmem := by
  simp only [restoreStates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The only emitted point in the epilogue is its actual RET successor. -/
theorem epilogue_observed (rxSection : Nat) (s : MachineData)
    (bx bp r12 r13 r14 ra : UInt64) :
    observeHistory (LookupObservation.edge rxSection)
      (⟨s, Image.Lookup.entry+0x89⟩ :: restoreStates s bx bp r12 r13 r14 ra) =
    .ok [LookupObservation.returned "wg_index_hashtable_lookup"
      ⟨restoreData s bx bp r12 r13 r14 6, .ofBitVec ra.toBitVec⟩] := by
  simp [observeHistory, restoreStates, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  rfl

#print axioms restoreStates_memory
#print axioms epilogue_observed

#print axioms epilogue_history
end Binary.LookupReturn
