import History
import LookupObservation
import Symbolic
import Regions

namespace Binary.LookupHistory

local instance : Labels := Image.linkedLabels

def compared (s : MachineData) : MachineData :=
  let a := s.regs.get (.low .rbp .W32)
  let b := s.regs.get (.low .r12 .W32)
  let v := a - b
  { s with status := StatusFlags.from_result v {
      cf := v.unsigned != a.unsigned - b.unsigned
      af := (v.take 4).unsigned != (a.take 4).unsigned - (b.take 4).unsigned
      of := v.signed != a.signed - b.signed } }

def indexHit (s : MachineData) : Bool :=
  (s.regs.get (.low .rbp .W32)).toNat == (s.regs.get (.low .r12 .W32)).toNat

def compareMiddle (s : MachineData) : MachineState :=
  ⟨compared s, Image.Lookup.entry + 0x5c⟩

def compareExit (s : MachineData) : MachineState :=
  ⟨compared s, if indexHit s then Image.Lookup.entry + 0x95 else Image.Lookup.entry + 0x5e⟩

private theorem fetch_cmp : Image.fetch (Image.Lookup.entry + 0x59) = some ⟨firstCompare, 3⟩ := by
  rfl

private theorem fetch_je : Image.fetch (Image.Lookup.entry + 0x5c) =
    some ⟨.regular .W64 .W64 (.jcc .z "L_ffffffff813a0505"), 2⟩ := by
  rfl

private theorem compare_nat (a b : BitVec 32) :
    (a - b == 0#32) = (a.toNat == b.toNat) := by
  apply Bool.eq_iff_iff.mpr
  simp [BitVec.sub_eq_iff_eq_add, BitVec.toNat_inj]

/-- Reuse a one-instruction region fact without losing its history. This
    covers all singleton instrumentation-call regions, including their real
    return-address push, and quantifies every instruction effect as before. -/
theorem singleton_region (fetch : Int64 → Option Decoded) (pc : Int64)
    (i : Instr) (n : Nat) (positive : n > 0)
    (here : fetch pc = some ⟨i, n⟩) (s : MachineData)
    (history : List MachineState) (P : MachineState → Prop)
    (run : (Directives.interp [⟨.instr i, n⟩] s pc (fun p d => .done ⟨d, p⟩)).All P) :
    historySteps fetch 1
      (fun t => P t.machine ∧ t.history = history ++ [t.machine]) ⟨⟨s, pc⟩, history⟩ := by
  apply instruction_history
  simp only [instructionStep, here]
  exact ⟨positive, run⟩

def tested {w : Width} (r : Reg w) (s : MachineData) (af : Bool) : MachineData :=
  { s with status := StatusFlags.from_result (s.regs.get r) {cf := false, af, of := false} }

def TestHistory {w : Width} (r : Reg w) (s : MachineData)
    (middlePc exitPc : Int64) (history : List MachineState) (t : Executed) : Prop :=
  ∃ af, t.machine = ⟨tested r s af, exitPc⟩ ∧
    t.history = history ++ [⟨tested r s af, middlePc⟩, ⟨tested r s af, exitPc⟩]

/-- The TEST/JE pattern retains the actual universally chosen AF value in
    its history. This does not select a canonical value for an undefined bit. -/
theorem test_self (fetch : Int64 → Option Decoded) (pc : Int64)
    (w : Width) (r : Reg w) (target : Label) (testSize jumpSize : Nat)
    (testPositive : 0 < testSize) (jumpPositive : 0 < jumpSize)
    (first : fetch pc = some ⟨.regular .W64 w (.test (.reg r) (.reg r)), testSize⟩)
    (second : fetch (pc + .ofNat testSize) =
      some ⟨.regular .W64 .W64 (.jcc .z target), jumpSize⟩)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory r s (pc + .ofNat testSize)
      (if s.regs.get r == 0 then label target else pc + .ofNat testSize + .ofNat jumpSize) history)
      ⟨⟨s, pc⟩, history⟩ := by
  unfold TestHistory
  simp only [historySteps, historyStep, instructionStep, first, second,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp, Effects.All]
  refine ⟨testPositive, fun af => ⟨jumpPositive, ?_⟩⟩
  simp only [StatusFlags.from_result, CondCode.interp, BitVec.and_self]
  cases hz : (s.regs.get r == 0) <;>
    simp_all [Effects.All, tested, StatusFlags.from_result, List.append_assoc]

/-- The TEST/JNE pattern retains the actual universally chosen AF value in
    its history. This does not select a canonical value for an undefined bit. -/
theorem test_self_nz (fetch : Int64 → Option Decoded) (pc : Int64)
    (w : Width) (r : Reg w) (target : Label) (testSize jumpSize : Nat)
    (testPositive : 0 < testSize) (jumpPositive : 0 < jumpSize)
    (first : fetch pc = some ⟨.regular .W64 w (.test (.reg r) (.reg r)), testSize⟩)
    (second : fetch (pc + .ofNat testSize) =
      some ⟨.regular .W64 .W64 (.jcc .nz target), jumpSize⟩)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory r s (pc + .ofNat testSize)
      (if s.regs.get r == 0 then pc + .ofNat testSize + .ofNat jumpSize else label target) history)
      ⟨⟨s, pc⟩, history⟩ := by
  unfold TestHistory
  simp only [historySteps, historyStep, instructionStep, first, second,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp, Effects.All]
  refine ⟨testPositive, fun af => ⟨jumpPositive, ?_⟩⟩
  simp only [StatusFlags.from_result, CondCode.interp, BitVec.and_self]
  cases hz : (s.regs.get r == 0) <;>
    simp_all [Effects.All, tested, StatusFlags.from_result, List.append_assoc]

/-- The two induction boundaries have the same head register and source
    phase (before idxWalk), despite opposite encodings of the branch. -/
theorem first_bucket_guard (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rbx .W64) s (Image.Lookup.entry + 0x32)
      (if s.regs.get (.low .rbx .W64) == 0 then Image.Lookup.entry + 0x6c else Image.Lookup.entry + 0x34) history)
      ⟨⟨s, Image.Lookup.entry + 0x2f⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff813a04dc" 3 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

theorem next_bucket_guard (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rbx .W64) s (Image.Lookup.entry + 0x6a)
      (if s.regs.get (.low .rbx .W64) == 0 then Image.Lookup.entry + 0x6c else Image.Lookup.entry + 0x34) history)
      ⟨⟨s, Image.Lookup.entry + 0x67⟩, history⟩ := by
  exact test_self_nz fetch _ _ _ "L_ffffffff813a04a4" 3 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms first_bucket_guard
#print axioms next_bucket_guard

theorem entry_guard (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rbx .W64) s (Image.Lookup.entry + 0x45)
      (if s.regs.get (.low .rbx .W64) == 0 then Image.Lookup.entry + 0x71 else Image.Lookup.entry + 0x47) history)
      ⟨⟨s, Image.Lookup.entry + 0x42⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff813a04e1" 3 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

theorem type_guard (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .r14 .W32) s (Image.Lookup.entry + 0xab)
      (if s.regs.get (.low .r14 .W32) == 0 then Image.Lookup.entry + 0x71 else Image.Lookup.entry + 0xad) history)
      ⟨⟨s, Image.Lookup.entry + 0xa8⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff813a04e1" 3 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

theorem peer_null_guard (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rbx .W64) s (Image.PeerGet.entry + 0x15)
      (if s.regs.get (.low .rbx .W64) == 0 then Image.PeerGet.entry + 0xdd else Image.PeerGet.entry + 0x1b) history)
      ⟨⟨s, Image.PeerGet.entry + 0x12⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff813996ed" 3 6 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

theorem peer_zero_guard (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rbp .W32) s (Image.PeerGet.entry + 0x3d)
      (if s.regs.get (.low .rbp .W32) == 0 then Image.PeerGet.entry + 0xb0 else Image.PeerGet.entry + 0x3f) history)
      ⟨⟨s, Image.PeerGet.entry + 0x3b⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff813996c0" 2 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

theorem peer_retry_guard (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .r15 .W8) s (Image.PeerGet.entry + 0x63)
      (if s.regs.get (.low .r15 .W8) == 0 then Image.PeerGet.entry + 0xf2 else Image.PeerGet.entry + 0x69) history)
      ⟨⟨s, Image.PeerGet.entry + 0x60⟩, history⟩ := by
  exact test_self fetch _ _ _ "L_ffffffff81399702" 3 6 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms test_self
#print axioms entry_guard
#print axioms type_guard
#print axioms peer_null_guard
#print axioms peer_zero_guard
#print axioms peer_retry_guard

/-- Exact history of both decoded instructions, for any ambient image that
    agrees on the anchored bytes. No endpoint-only fact supplies the history. -/
theorem index_compare (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2
      (fun t => t.machine = compareExit s ∧
        t.history = history ++ [compareMiddle s, compareExit s])
      ⟨⟨s, Image.Lookup.entry + 0x59⟩, history⟩ := by
  have first := agree _ _ fetch_cmp
  have second := agree _ _ fetch_je
  have nextAddress : Image.Lookup.entry + 0x59 + Int64.ofNat 3 = Image.Lookup.entry + 0x5c := rfl
  simp only [historySteps, historyStep, instructionStep, first, nextAddress, second,
    firstCompare, Instr.interp, Operation.interp, RegOrMem.interp,
    Operand.interp, Effects.All]
  change 0 < 3 ∧ (0 < 2 ∧ _)
  refine ⟨by decide, by decide, ?_⟩
  simp [StatusFlags.from_result, CondCode.interp, compare_nat,
    compareExit, compareMiddle, compared, indexHit, Image.Lookup.entry]
  split <;> simp_all [Effects.All] <;> rfl

/-- The observer reads the actual two edges, retaining the precise outcome
    and the machine state at that decision. -/
theorem index_compare_observation (rxSection : Nat) (s : MachineData) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.Lookup.entry + 0x59⟩, compareMiddle s, compareExit s] =
    .ok [LookupObservation.decision rxSection .idxMatch (indexHit s) (compareExit s)] := by
  cases h : indexHit s <;>
    simp [observeHistory, LookupObservation.edge, LookupObservation.choice,
      compareMiddle, compareExit, Image.Lookup.entry, Image.PeerGet.entry, h]
      <;> rfl

#print axioms index_compare
#print axioms index_compare_observation
end Binary.LookupHistory
