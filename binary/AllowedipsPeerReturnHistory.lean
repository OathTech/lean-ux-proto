import PeerLiveEntryHistory
import AllowedipsPeerCoverageHistory
import PeerReturn
import HistoryRegions

set_option maxHeartbeats 400000
set_option maxRecDepth 16384

namespace Binary.AllowedipsPeerGet
open PeerGet LookupHistory
local instance : Labels := Image.linkedLabels

/-- The actual register file after each epilogue instruction, including
    the return. Memory and flags are unchanged. -/
def restoreData (s : MachineData) (bx bp r12 r13 r14 r15 : UInt64) (n : Nat) : MachineData :=
  {s with regs := {s.regs with
    rax := s.regs.rbx
    rbx := if 1 ≤ n then bx else s.regs.rbx
    rbp := if 2 ≤ n then bp else s.regs.rbp
    r12 := if 3 ≤ n then r12 else s.regs.r12
    r13 := if 4 ≤ n then r13 else s.regs.r13
    r14 := if 5 ≤ n then r14 else s.regs.r14
    r15 := if 6 ≤ n then r15 else s.regs.r15
    rsp := s.regs.rsp + UInt64.ofNat (8 * min n 7)}}

def restoreStates (s : MachineData) (bx bp r12 r13 r14 r15 ra : UInt64) : List MachineState :=
  [⟨restoreData s bx bp r12 r13 r14 r15 0, Image.PeerGet.entry+0xa5⟩,
   ⟨restoreData s bx bp r12 r13 r14 r15 1, Image.PeerGet.entry+0xa6⟩,
   ⟨restoreData s bx bp r12 r13 r14 r15 2, Image.PeerGet.entry+0xa7⟩,
   ⟨restoreData s bx bp r12 r13 r14 r15 3, Image.PeerGet.entry+0xa9⟩,
   ⟨restoreData s bx bp r12 r13 r14 r15 4, Image.PeerGet.entry+0xab⟩,
   ⟨restoreData s bx bp r12 r13 r14 r15 5, Image.PeerGet.entry+0xad⟩,
   ⟨restoreData s bx bp r12 r13 r14 r15 6, Image.PeerGet.entry+0xaf⟩,
   ⟨restoreData s bx bp r12 r13 r14 r15 7, .ofBitVec ra.toBitVec⟩]

private theorem history_cons (fetch : Int64 → Option Decoded) (s next : MachineState)
    (history : List MachineState) (n : Nat) (P : Executed → Prop)
    (first : instructionStep fetch s (fun t => t = next))
    (rest : historySteps fetch n P ⟨next, history ++ [next]⟩) :
    historySteps fetch (n+1) P ⟨s, history⟩ := by
  exact instruction_mono fetch s (fun t => t = next) _ (fun t ht => ht ▸ rest) first

private theorem return_instruction0 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (r15.toNat : Int))
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨s, Image.PeerGet.entry+0xa2⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 r15 0, Image.PeerGet.entry+0xa5⟩) := by
  have f0 := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xa2) = some _ from rfl)
  simp only [instructionStep, f0]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, h6, restoreData] <;> try rfl

private theorem return_instruction1 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (r15.toNat : Int))
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 r15 0, Image.PeerGet.entry+0xa5⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 r15 1, Image.PeerGet.entry+0xa6⟩) := by
  have f1 := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xa5) = some _ from rfl)
  simp only [instructionStep, f1]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, h6, restoreData] <;> try rfl

private theorem return_instruction2 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (r15.toNat : Int))
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 r15 1, Image.PeerGet.entry+0xa6⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 r15 2, Image.PeerGet.entry+0xa7⟩) := by
  have f2 := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xa6) = some _ from rfl)
  simp only [instructionStep, f2]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, h6, restoreData] <;> try rfl
  try rw [h1]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]

private theorem return_instruction3 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (r15.toNat : Int))
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 r15 2, Image.PeerGet.entry+0xa7⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 r15 3, Image.PeerGet.entry+0xa9⟩) := by
  have f3 := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xa7) = some _ from rfl)
  simp only [instructionStep, f3]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, h6, restoreData] <;> try rfl
  try rw [h2]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]

private theorem return_instruction4 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (r15.toNat : Int))
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 r15 3, Image.PeerGet.entry+0xa9⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 r15 4, Image.PeerGet.entry+0xab⟩) := by
  have f4 := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xa9) = some _ from rfl)
  simp only [instructionStep, f4]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, h6, restoreData] <;> try rfl
  try rw [h3]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]

private theorem return_instruction5 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (r15.toNat : Int))
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 r15 4, Image.PeerGet.entry+0xab⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 r15 5, Image.PeerGet.entry+0xad⟩) := by
  have f5 := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xab) = some _ from rfl)
  simp only [instructionStep, f5]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, h6, restoreData] <;> try rfl
  try rw [h4]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]

private theorem return_instruction6 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (r15.toNat : Int))
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 r15 5, Image.PeerGet.entry+0xad⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 r15 6, Image.PeerGet.entry+0xaf⟩) := by
  have f6 := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xad) = some _ from rfl)
  simp only [instructionStep, f6]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, h6, restoreData] <;> try rfl
  try rw [h5]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]

private theorem return_instruction7 (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (r15.toNat : Int))
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48#64) 8 = some (ra.toNat : Int)) :
    instructionStep fetch ⟨restoreData s bx bp r12 r13 r14 r15 6, Image.PeerGet.entry+0xaf⟩
      (fun t => t = ⟨restoreData s bx bp r12 r13 r14 r15 7, .ofBitVec ra.toBitVec⟩) := by
  have f7 := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xaf) = some _ from rfl)
  simp only [instructionStep, f7]
  refine ⟨by decide, ?_⟩
  simp [
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, Effects.All, MachineData.set, MachineData.setReg,
    Reg64s.set, Reg64s.set64, BitVec.ofInt_ofNat,
    UInt64.toBitVec_add, UInt64.ofBitVec_add, BitVec.add_assoc,
    UInt64.add_assoc, h0, h1, h2, h3, h4, h5, h6, restoreData] <;> try rfl
  try rw [h6]
  all_goals first | rfl | exact ⟨rfl, rfl⟩ | simp [Effects.All, BitVec.ofInt_ofNat, UInt64.ofBitVec_add, BitVec.add_assoc]
  all_goals apply Int64.toBitVec_inj.mp
  all_goals simp [Image.PeerGet.entry]

theorem epilogue_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) (bx bp r12 r13 r14 r15 ra : UInt64)
    (h0 : s.dmem.loadInt s.regs.rsp.toBitVec 8 = some (bx.toNat : Int))
    (h1 : s.dmem.loadInt (s.regs.rsp.toBitVec+8#64) 8 = some (bp.toNat : Int))
    (h2 : s.dmem.loadInt (s.regs.rsp.toBitVec+16#64) 8 = some (r12.toNat : Int))
    (h3 : s.dmem.loadInt (s.regs.rsp.toBitVec+24#64) 8 = some (r13.toNat : Int))
    (h4 : s.dmem.loadInt (s.regs.rsp.toBitVec+32#64) 8 = some (r14.toNat : Int))
    (h5 : s.dmem.loadInt (s.regs.rsp.toBitVec+40#64) 8 = some (r15.toNat : Int))
    (h6 : s.dmem.loadInt (s.regs.rsp.toBitVec+48#64) 8 = some (ra.toNat : Int)) :
    historySteps fetch 8 (fun t =>
      t.machine = ⟨restoreData s bx bp r12 r13 r14 r15 7, .ofBitVec ra.toBitVec⟩ ∧
      t.history = history ++ restoreStates s bx bp r12 r13 r14 r15 ra)
      ⟨⟨s, Image.PeerGet.entry+0xa2⟩, history⟩ := by
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 r15 0, Image.PeerGet.entry+0xa5⟩
  · exact return_instruction0 fetch agree s history bx bp r12 r13 r14 r15 ra h0 h1 h2 h3 h4 h5 h6
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 r15 1, Image.PeerGet.entry+0xa6⟩
  · exact return_instruction1 fetch agree s history bx bp r12 r13 r14 r15 ra h0 h1 h2 h3 h4 h5 h6
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 r15 2, Image.PeerGet.entry+0xa7⟩
  · exact return_instruction2 fetch agree s history bx bp r12 r13 r14 r15 ra h0 h1 h2 h3 h4 h5 h6
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 r15 3, Image.PeerGet.entry+0xa9⟩
  · exact return_instruction3 fetch agree s history bx bp r12 r13 r14 r15 ra h0 h1 h2 h3 h4 h5 h6
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 r15 4, Image.PeerGet.entry+0xab⟩
  · exact return_instruction4 fetch agree s history bx bp r12 r13 r14 r15 ra h0 h1 h2 h3 h4 h5 h6
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 r15 5, Image.PeerGet.entry+0xad⟩
  · exact return_instruction5 fetch agree s history bx bp r12 r13 r14 r15 ra h0 h1 h2 h3 h4 h5 h6
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 r15 6, Image.PeerGet.entry+0xaf⟩
  · exact return_instruction6 fetch agree s history bx bp r12 r13 r14 r15 ra h0 h1 h2 h3 h4 h5 h6
  apply history_cons fetch _ ⟨restoreData s bx bp r12 r13 r14 r15 7, .ofBitVec ra.toBitVec⟩
  · exact return_instruction7 fetch agree s history bx bp r12 r13 r14 r15 ra h0 h1 h2 h3 h4 h5 h6
  simp [historySteps, restoreStates, List.append_assoc]


/-- Every actual epilogue successor preserves all memory, including the
    owner peer word and the complete physical World footprint. -/
theorem restoreStates_memory (s : MachineData) (bx bp r12 r13 r14 r15 ra : UInt64)
    (t : MachineState) (member : t ∈ restoreStates s bx bp r12 r13 r14 r15 ra) :
    t.data.dmem = s.dmem := by
  simp only [restoreStates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

/-- The only emitted point in the epilogue is its actual RET successor. -/
theorem epilogue_observed (rxSection : Nat) (s : MachineData)
    (bx bp r12 r13 r14 r15 ra : UInt64) :
    observeHistory (AllowedipsPeerObservation.edge rxSection)
      (⟨s, Image.PeerGet.entry+0xa2⟩ :: restoreStates s bx bp r12 r13 r14 r15 ra) =
    .ok [LookupObservation.returned "wg_peer_get_maybe_zero"
      ⟨restoreData s bx bp r12 r13 r14 r15 7, .ofBitVec ra.toBitVec⟩] := by
  simp [observeHistory, restoreStates, AllowedipsPeerObservation.edge, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  rfl

#print axioms restoreStates_memory
#print axioms epilogue_observed

#print axioms epilogue_history
end Binary.AllowedipsPeerGet
