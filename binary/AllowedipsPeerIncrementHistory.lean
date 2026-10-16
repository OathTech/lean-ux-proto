import PeerLiveEntryHistory
import AllowedipsPeerCoverageHistory
import PeerIncrement
import AllowedipsPeerCompareHistory

set_option maxHeartbeats 1000000
namespace Binary.AllowedipsPeerGet
open PeerGet LookupHistory
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

private theorem low32 (v : UInt64) :
    BitVec.ofInt 32 ((v.toNat : Int) % 4294967296) = v.toBitVec.extractLsb' 0 32 := by
  apply BitVec.eq_of_toNat_eq
  simp
  exact Int.toNat_emod (by omega) (by decide)

private theorem truncate_extend (v : BitVec 32) :
    (v.setWidth 64).extractLsb' 0 32 = v := by
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

private theorem lea_low32 (v : UInt64) :
    (v.toBitVec + 1#64).setWidth 32 = v.toBitVec.extractLsb' 0 32 + 1 := by
  rw [BitVec.setWidth_add _ _ (by decide)]
  rw [BitVec.setWidth_eq_extractLsb' (by decide)]
  rfl

private theorem mod32_64 (i : Int) :
    (i % 4294967296) % 18446744073709551616 = i % 4294967296 := by
  have h0 := Int.emod_nonneg i (by decide : (4294967296 : Int) ≠ 0)
  have h1 := Int.emod_lt_of_pos i (by decide : (0 : Int) < 4294967296)
  omega


def incLea (s : MachineData) : MachineData :=
  s.setReg (.low .r12 .W32) (s.regs.get (.low .rbp .W32)+1)
def incMove (s : MachineData) : MachineData :=
  (incLea s).setReg (.low .rax .W32) (s.regs.get (.low .rbp .W32))
def incCompare (s : MachineData) : MachineData :=
  {incMove s with dmem := incrementMemory s, status := StatusFlags.from_result (0#32) {cf := false, af := false, of := false}}
def incSet (s : MachineData) : MachineData :=
  (incCompare s).setReg (.low .r15 .W8) 1


/-- Actual LEA, including truncation of the 64-bit effective address to R12D. -/
theorem inc_lea_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (s : MachineData) (history : List MachineState) :
    historySteps fetch 1 (fun t => t.machine = ⟨incLea s, Image.PeerGet.entry+0x48⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, Image.PeerGet.entry+0x44⟩, history⟩ := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+0x44) = some _ from rfl)
  refine instruction_history fetch ⟨s, Image.PeerGet.entry+0x44⟩ history
    (fun t => t = ⟨incLea s, Image.PeerGet.entry+0x48⟩) ?_
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, MachineData.setReg, AddrExpr.interp,
    Reg64s.get, Reg64s.get64, Reg64s.set, Reg64s.set64, Reg.base, Reg.offset,
    BitVec.drop, BitVec.take, ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat, Effects.All,
    incLea, Image.PeerGet.entry, lea_low32]

/-- Successful compare/exchange retains the exact subtraction flags. -/
theorem inc_cmpxchg_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (s : MachineData) (history : List MachineState)
    (count : s.dmem.loadInt s.regs.r13.toBitVec 4 = some (s.regs.get (.low .rbp .W32)).toNat) :
    historySteps fetch 1 (fun t => t.machine = ⟨incCompare s, Image.PeerGet.entry+0x4f⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨incMove s, Image.PeerGet.entry+0x4a⟩, history⟩ := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+0x4a) = some _ from rfl)
  refine instruction_history fetch ⟨incMove s, Image.PeerGet.entry+0x4a⟩ history
    (fun t => t = ⟨incCompare s, Image.PeerGet.entry+0x4f⟩) ?_
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.store, MachineData.set, MachineData.setReg,
    AddrExpr.interp, Reg64s.get, Reg64s.get64, Reg.base, Reg.offset,
    Reg64s.set, Reg64s.set64, BitVec.drop, BitVec.take,
    ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    Effects.All, StatusFlags.from_result, Width.bytesv,
    incLea, incMove, incCompare, incrementMemory, Image.PeerGet.entry] at count ⊢
  simp_all [Effects.All, low32, truncate_extend, mod32_64, Int.emod_bmod]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide), BitVec.extractLsb'_extractLsb'_of_le (by decide)]
  simp [BitVec.unsigned]

/-- SETE writes just R15B. Its upper bytes are deliberately not cleared. -/
theorem inc_set_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (s : MachineData) (history : List MachineState) :
    historySteps fetch 1 (fun t => t.machine = ⟨incSet s, Image.PeerGet.entry+0x53⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨incCompare s, Image.PeerGet.entry+0x4f⟩, history⟩ := by
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+0x4f) = some _ from rfl)
  refine instruction_history fetch ⟨incCompare s, Image.PeerGet.entry+0x4f⟩ history
    (fun t => t = ⟨incSet s, Image.PeerGet.entry+0x53⟩) ?_
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, MachineData.set,
    CondCode.interp, incCompare, incSet, Effects.All, StatusFlags.from_result, Image.PeerGet.entry]


/-- All four successors before XOR's undefined AF choice. -/
theorem increment_first_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (s : MachineData) (history : List MachineState)
    (count : s.dmem.loadInt s.regs.r13.toBitVec 4 = some (s.regs.get (.low .rbp .W32)).toNat) :
    historySteps fetch 4 (fun t => t.machine = ⟨incSet s, Image.PeerGet.entry+0x53⟩ ∧
      t.history = history ++ [⟨incLea s, Image.PeerGet.entry+0x48⟩,
        ⟨incMove s, Image.PeerGet.entry+0x4a⟩, ⟨incCompare s, Image.PeerGet.entry+0x4f⟩, t.machine])
      ⟨⟨s, Image.PeerGet.entry+0x44⟩, history⟩ := by
  rw [show 4 = 1+3 from rfl, historySteps_add]
  have step0 := inc_lea_history fetch agree s history
  apply historySteps_mono fetch 1 _ _ _ _ step0
  rintro t ⟨machine, recorded⟩
  have machine0 : t.machine = (⟨incLea s, Image.PeerGet.entry+0x48⟩ : MachineState) := machine
  have cursor : t = ⟨(⟨incLea s, Image.PeerGet.entry+0x48⟩ : MachineState), history ++ [(⟨incLea s, Image.PeerGet.entry+0x48⟩ : MachineState)]⟩ := by
    cases t; simp_all [List.append_assoc]
  rw [cursor]
  rw [show 3 = 1+2 from rfl, historySteps_add]
  have step1 := mov32_history fetch (Image.PeerGet.entry+0x48) (.low .rax .W32) (.low .rbp .W32) 2 (by decide) (agree _ _ (by rfl)) (incLea s) (history ++ [(⟨incLea s, Image.PeerGet.entry+0x48⟩ : MachineState)])
  apply historySteps_mono fetch 1 _ _ _ _ step1
  rintro t ⟨machine, recorded⟩
  have machine1 : t.machine = (⟨incMove s, Image.PeerGet.entry+0x4a⟩ : MachineState) := machine
  have cursor : t = ⟨(⟨incMove s, Image.PeerGet.entry+0x4a⟩ : MachineState), history ++ [(⟨incLea s, Image.PeerGet.entry+0x48⟩ : MachineState), (⟨incMove s, Image.PeerGet.entry+0x4a⟩ : MachineState)]⟩ := by
    cases t; simp_all [List.append_assoc]
  rw [cursor]
  rw [show 2 = 1+1 from rfl, historySteps_add]
  have step2 := inc_cmpxchg_history fetch agree s (history ++ [(⟨incLea s, Image.PeerGet.entry+0x48⟩ : MachineState), (⟨incMove s, Image.PeerGet.entry+0x4a⟩ : MachineState)]) count
  apply historySteps_mono fetch 1 _ _ _ _ step2
  rintro t ⟨machine, recorded⟩
  have machine2 : t.machine = (⟨incCompare s, Image.PeerGet.entry+0x4f⟩ : MachineState) := machine
  have cursor : t = ⟨(⟨incCompare s, Image.PeerGet.entry+0x4f⟩ : MachineState), history ++ [(⟨incLea s, Image.PeerGet.entry+0x48⟩ : MachineState), (⟨incMove s, Image.PeerGet.entry+0x4a⟩ : MachineState), (⟨incCompare s, Image.PeerGet.entry+0x4f⟩ : MachineState)]⟩ := by
    cases t; simp_all [List.append_assoc]
  rw [cursor]
  have step3 := inc_set_history fetch agree s (history ++ [(⟨incLea s, Image.PeerGet.entry+0x48⟩ : MachineState), (⟨incMove s, Image.PeerGet.entry+0x4a⟩ : MachineState), (⟨incCompare s, Image.PeerGet.entry+0x4f⟩ : MachineState)])
  apply historySteps_mono fetch 1 _ _ _ _ step3
  rintro t ⟨machine, recorded⟩
  exact ⟨machine, by simpa only [List.append_assoc, List.cons_append, List.nil_append] using recorded⟩

def incXor (s : MachineData) (af : Bool) : MachineData := zeroed (incSet s) (.low .rdi .W32) af
def incCopy (s : MachineData) (af : Bool) : MachineData :=
  (incXor s af).setReg (.low .r14 .W32) ((incXor s af).regs.get (.low .rax .W32))
def incFinal (s : MachineData) (af : Bool) : MachineData :=
  (incCopy s af).setReg (.low .rsi .W32) ((incCopy s af).regs.get (.low .r15 .W32))

def incrementStates (s : MachineData) (af : Bool) : List MachineState :=
  [⟨incLea s, Image.PeerGet.entry+0x48⟩, ⟨incMove s, Image.PeerGet.entry+0x4a⟩,
   ⟨incCompare s, Image.PeerGet.entry+0x4f⟩, ⟨incSet s, Image.PeerGet.entry+0x53⟩,
   ⟨incXor s af, Image.PeerGet.entry+0x55⟩, ⟨incCopy s af, Image.PeerGet.entry+0x58⟩,
   ⟨incFinal s af, Image.PeerGet.entry+0x5b⟩]

/-- Seven actual instructions, including the exact CMPXCHG flags before
    XOR and the universally chosen AF afterwards. Stops before the CALL. -/
theorem increment_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (s : MachineData) (history : List MachineState)
    (count : s.dmem.loadInt s.regs.r13.toBitVec 4 = some (s.regs.get (.low .rbp .W32)).toNat) :
    historySteps fetch 7 (fun t => ∃ af,
      t.machine = ⟨incFinal s af, Image.PeerGet.entry+0x5b⟩ ∧
      t.history = history ++ incrementStates s af)
      ⟨⟨s, Image.PeerGet.entry+0x44⟩, history⟩ := by
  rw [show 7 = 4+3 from rfl, historySteps_add]
  apply historySteps_mono fetch 4 _ _ _ _ (increment_first_history fetch agree s history count)
  rintro t ⟨machine, recorded⟩
  let first : List MachineState := [⟨incLea s, Image.PeerGet.entry+0x48⟩,
    ⟨incMove s, Image.PeerGet.entry+0x4a⟩, ⟨incCompare s, Image.PeerGet.entry+0x4f⟩,
    ⟨incSet s, Image.PeerGet.entry+0x53⟩]
  have cursor : t = ⟨⟨incSet s, Image.PeerGet.entry+0x53⟩, history ++ first⟩ := by cases t; simp_all [first]
  rw [cursor, show 3 = 1+2 from rfl, historySteps_add]
  have step := xor32_history fetch (Image.PeerGet.entry+0x53) 2 (.low .rdi .W32)
    (by decide) (agree _ _ (by rfl)) (incSet s) (history ++ first)
  apply historySteps_mono fetch 1 _ _ _ _ step
  rintro t ⟨af, machine, recorded⟩
  have machine₁ : t.machine = ⟨incXor s af, Image.PeerGet.entry+0x55⟩ := machine
  have cursor : t = ⟨⟨incXor s af, Image.PeerGet.entry+0x55⟩,
      (history ++ first) ++ [⟨incXor s af, Image.PeerGet.entry+0x55⟩]⟩ := by cases t; simp_all
  rw [cursor, show 2 = 1+1 from rfl, historySteps_add]
  have step := mov32_history fetch (Image.PeerGet.entry+0x55) (.low .r14 .W32) (.low .rax .W32)
    3 (by decide) (agree _ _ (by rfl)) (incXor s af)
    ((history ++ first) ++ [(⟨incXor s af, Image.PeerGet.entry+0x55⟩ : MachineState)])
  apply historySteps_mono fetch 1 _ _ _ _ step
  rintro t ⟨machine, recorded⟩
  have machine₂ : t.machine = ⟨incCopy s af, Image.PeerGet.entry+0x58⟩ := machine
  have cursor : t = ⟨⟨incCopy s af, Image.PeerGet.entry+0x58⟩,
      (history ++ first) ++ [⟨incXor s af, Image.PeerGet.entry+0x55⟩, ⟨incCopy s af, Image.PeerGet.entry+0x58⟩]⟩ := by
    cases t; simp_all [List.append_assoc]
  rw [cursor]
  have step := mov32_history fetch (Image.PeerGet.entry+0x58) (.low .rsi .W32) (.low .r15 .W32)
    3 (by decide) (agree _ _ (by rfl)) (incCopy s af)
    ((history ++ first) ++ [(⟨incXor s af, Image.PeerGet.entry+0x55⟩ : MachineState),
      ⟨incCopy s af, Image.PeerGet.entry+0x58⟩])
  apply historySteps_mono fetch 1 _ _ _ _ step
  rintro t ⟨machine, recorded⟩
  refine ⟨af, machine, ?_⟩
  simpa only [machine, incFinal, incrementStates, first, List.append_assoc,
    List.cons_append, List.nil_append,
    show Image.PeerGet.entry+0x58+Int64.ofNat 3 = Image.PeerGet.entry+0x5b from rfl] using recorded

#print axioms increment_first_history
#print axioms increment_history
#print axioms inc_lea_history
#print axioms inc_cmpxchg_history
#print axioms inc_set_history

/-- The old endpoint abstraction omitted flags. The actual successor has
    XOR's zero-result flags and its independently quantified AF. -/
theorem incFinal_shape (s : MachineData) (af : Bool) :
    incFinal s af = {incremented s with
      status := StatusFlags.from_result (0#32) {cf := false, af, of := false}} := by
  simp [incFinal, incCopy, incXor, zeroed, incSet, incCompare, incMove, incLea,
    incremented, incrementRegisters, MachineData.setReg, Reg64s.set, Reg64s.set64,
    Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.take, BitVec.drop,
    BitVec.replaceLow]
  rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
  simp

/-- The increment region emits no mirror decision before the byte callback. -/
theorem increment_observed (rxSection : Nat) (s : MachineData) (af : Bool) :
    observeHistory (AllowedipsPeerObservation.edge rxSection)
      (⟨s, Image.PeerGet.entry+0x44⟩ :: incrementStates s af) = .ok [] := by
  simp [incrementStates, observeHistory, AllowedipsPeerObservation.edge, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]

/-- All actual intermediate states remain recorded; the only new anchored
    cut before the CALL is its argument state at +0x5b. -/
theorem increment_cuts (s : MachineData) (af : Bool) (q : MachineState)
    (member : q ∈ incrementStates s af) (cut : (q.pc ∈ AllowedipsImage.cutPoints ∨ q.pc ∈ Image.cutPoints)) :
    q = ⟨incFinal s af, Image.PeerGet.entry+0x5b⟩ := by
  simp only [incrementStates, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals dsimp only at cut
  all_goals first | rfl | exact absurd cut (by decide)

#print axioms incFinal_shape
#print axioms increment_observed
#print axioms increment_cuts

end Binary.AllowedipsPeerGet
