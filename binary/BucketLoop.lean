import HistoryRegions
import Representation

namespace Binary.LookupHistory
local instance : Labels := Image.linkedLabels

def nextData (s : MachineData) (next : UInt64) : MachineData :=
  {s with regs := {s.regs with rbx := next}}

/-- The tail load stops before idxWalk, exactly at the induction boundary. -/
theorem next_load (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (next : UInt64) (history : List MachineState)
    (loaded : s.dmem.loadInt (s.regs.rbx.toBitVec + 8) 8 = some next.toNat) :
    historySteps fetch 1
      (fun t => t.machine = ⟨nextData s next, Image.Lookup.entry + 0x67⟩ ∧
        t.history = history ++ [t.machine])
      ⟨⟨s, Image.Lookup.entry + 0x63⟩, history⟩ := by
  refine instruction_history fetch ⟨s, Image.Lookup.entry + 0x63⟩ history
    (fun t => t = ⟨nextData s next, Image.Lookup.entry + 0x67⟩) ?_
  have here := agree (Image.Lookup.entry + 0x63)
    ⟨.regular .W64 .W64 (.mov (.reg (.low .rbx .W64))
      (.regOrMem (.mem {base := some (.reg .rbx), idx := none, disp := .int64 8}))), 4⟩ (by rfl)
  simp only [instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp,
    MachineData.load, MachineData.set, MachineData.setReg,
    AddrExpr.interp,  Reg64s.get64,
    Reg64s.set, Reg64s.set64,  BitVec.take,
    ConstExpr.interp, BitVec.toAddressSize, BitVec.signed,
    BitVec.ofInt_add, BitVec.ofInt_toInt, BitVec.ofInt_ofNat,
    Effects.All, loaded, nextData, Image.Lookup.entry] at loaded ⊢

/-- A real pointer load advances the intrusive-list component of R to its
    actual tail. Every other physical byte is unchanged; no distinct-index
    or positive-peer-count premise is introduced. This is one part of the
    full loop invariant, not a whole-function simulation. -/
theorem next_load_bucket (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData)
    (entry : Leanux.WG.IndexEntry) (rest : List (Address × Leanux.WG.IndexEntry))
    (history : List MachineState)
    (bucket : BucketShape s.dmem (s.regs.rbx.toBitVec + 8)
      ((s.regs.rbx.toBitVec, entry) :: rest)) :
    historySteps fetch 1
      (fun t => t.machine.pc = Image.Lookup.entry + 0x67 ∧
        t.machine.data.dmem = s.dmem ∧
        BucketShape t.machine.data.dmem t.machine.data.regs.rbx.toBitVec rest ∧
        t.history = history ++ [t.machine])
      ⟨⟨s, Image.Lookup.entry + 0x63⟩, history⟩ := by
  obtain ⟨next, loaded, tail⟩ := bucket_tail s.dmem _ _ _ _ bucket
  simp only [Layouts.node_next, BitVec.add_zero] at loaded
  apply historySteps_mono fetch 1 _ _ _ _
    (next_load fetch agree s (.ofBitVec next) history loaded)
  rintro t ⟨machine, history⟩
  rw [machine] at *
  exact ⟨rfl, rfl, tail, history⟩

def walkExit (s : MachineData) (af : Bool) : MachineState :=
  ⟨tested (.low .rbx .W64) s af,
    if s.regs.get (.low .rbx .W64) == 0 then Image.Lookup.entry + 0x6c else Image.Lookup.entry + 0x34⟩

def walkPoints (rxSection : Nat) (s : MachineData) (af : Bool) : List LookupObservation.Point :=
  let more := decide (s.regs.get (.low .rbx .W64) ≠ 0)
  [LookupObservation.decision rxSection .idxWalk more (walkExit s af)] ++
    (if more then [] else [LookupObservation.decision rxSection .idxFound false (walkExit s af)])

/-- Both machine guards emit the same mirror-phase events, including the
    second, merged event on an empty bucket. -/
theorem first_walk_observation (rxSection : Nat) (s : MachineData) (af : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.Lookup.entry + 0x2f⟩,
       ⟨tested (.low .rbx .W64) s af, Image.Lookup.entry + 0x32⟩, walkExit s af] =
      .ok (walkPoints rxSection s af) := by
  by_cases h : s.regs.get (.low .rbx .W64) = 0#64 <;>
    simp [observeHistory, LookupObservation.edge, LookupObservation.choice,
      walkExit, walkPoints, Image.Lookup.entry, Image.PeerGet.entry, h] <;> rfl

theorem next_walk_observation (rxSection : Nat) (s : MachineData) (af : Bool) :
    observeHistory (LookupObservation.edge rxSection)
      [⟨s, Image.Lookup.entry + 0x67⟩,
       ⟨tested (.low .rbx .W64) s af, Image.Lookup.entry + 0x6a⟩, walkExit s af] =
      .ok (walkPoints rxSection s af) := by
  by_cases h : s.regs.get (.low .rbx .W64) = 0#64 <;>
    simp [observeHistory, LookupObservation.edge, LookupObservation.choice,
      walkExit, walkPoints, Image.Lookup.entry, Image.PeerGet.entry, h] <;> rfl

/-- The physical loop invariant survives the tail load and the following
    guard as one actual three-instruction execution. The remaining list,
    including an empty list, determines the guard; peer words are unread. -/
theorem tail_iteration (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (entry : Leanux.WG.IndexEntry)
    (rest : List (Address × Leanux.WG.IndexEntry)) (history : List MachineState)
    (bucket : BucketShape s.dmem (s.regs.rbx.toBitVec + 8)
      ((s.regs.rbx.toBitVec, entry) :: rest)) :
    historySteps fetch 3 (fun t => ∃ next : UInt64, ∃ af : Bool,
      t.machine = walkExit (nextData s next) af ∧
      t.history = history ++ [⟨nextData s next, Image.Lookup.entry + 0x67⟩,
        ⟨tested (.low .rbx .W64) (nextData s next) af, Image.Lookup.entry + 0x6a⟩,
        walkExit (nextData s next) af] ∧
      BucketShape t.machine.data.dmem next.toBitVec rest ∧
      t.machine.data.dmem = s.dmem ∧
      (next = 0 ↔ rest = []))
      ⟨⟨s, Image.Lookup.entry + 0x63⟩, history⟩ := by
  obtain ⟨next, loaded, tail⟩ := bucket_tail _ _ _ _ _ bucket
  simp only [Layouts.node_next, BitVec.add_zero] at loaded
  rw [show 3 = 1+2 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _
    (next_load fetch agree s (.ofBitVec next) history loaded)
  rintro t ⟨machine, recorded⟩
  have state : t = ⟨⟨nextData s (.ofBitVec next), Image.Lookup.entry + 0x67⟩,
      history ++ [⟨nextData s (.ofBitVec next), Image.Lookup.entry + 0x67⟩]⟩ := by
    cases t
    simp_all
  rw [state]
  apply historySteps_mono fetch 2 _ _ _ _
    (next_bucket_guard fetch agree (nextData s (.ofBitVec next)) _)
  rintro u ⟨af, machine, recorded⟩
  refine ⟨.ofBitVec next, af, machine, ?_, ?_, ?_, ?_⟩
  · simpa only [List.append_assoc, List.cons_append, List.nil_append, walkExit] using recorded
  · rw [machine]
    exact tail
  · rw [machine]
    rfl
  · rw [← UInt64.toBitVec_inj]
    exact tail.head_zero_iff

#print axioms tail_iteration

#print axioms first_walk_observation
#print axioms next_walk_observation
#print axioms next_load
#print axioms next_load_bucket
end Binary.LookupHistory
