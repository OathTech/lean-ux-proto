import PeerLiveEntryHistory
import AllowedipsPeerCoverageHistory
import HistoryRegions
import TrustBase

namespace Binary.AllowedipsPeerGet
open PeerGet LookupHistory
local instance : Labels := Image.linkedLabels

def zeroed (s : MachineData) (r : Reg .W32) (af : Bool) : MachineData :=
  {s with status := StatusFlags.from_result (0#32) {cf := false, of := false, af}}.setReg r 0

/-- XOR's chosen AF is retained in the actual successor; the destination
    uses the architectural 32-bit write, including upper-word clearing. -/
theorem xor32_history (fetch : Int64 → Option Decoded) (pc : Int64) (size : Nat)
    (r : Reg .W32) (positive : 0 < size)
    (here : fetch pc = some ⟨.regular .W64 .W32 (.xor (.reg r) (.regOrMem (.reg r))), size⟩)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 1 (fun t => ∃ af,
      t.machine = ⟨zeroed s r af, pc + .ofNat size⟩ ∧
      t.history = history ++ [t.machine]) ⟨⟨s, pc⟩, history⟩ := by
  simp only [historySteps, historyStep, instructionStep, here]
  refine ⟨positive, ?_⟩
  simp only [Instr.interp, Operation.interp, Operand.interp, RegOrMem.interp,
    Effects.All, BitVec.xor_self, MachineData.set]
  intro af
  exact ⟨af, rfl, trivial⟩

/-- The shared clear-peer branch has exactly two real successors and no
    source decision. Null and dead callers both use it. -/
theorem clear_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨zeroed s (.low .rbx .W32) af, Image.PeerGet.entry+0x9d⟩ ∧
      t.history = history ++ [⟨zeroed s (.low .rbx .W32) af, Image.PeerGet.entry+0xdf⟩,
        ⟨zeroed s (.low .rbx .W32) af, Image.PeerGet.entry+0x9d⟩])
      ⟨⟨s, Image.PeerGet.entry+0xdd⟩, history⟩ := by
  rw [show 2 = 1+1 from rfl, historySteps_add]
  apply historySteps_mono fetch 1 _ _ _ _
    (xor32_history fetch (Image.PeerGet.entry+0xdd) 2 (.low .rbx .W32) (by decide)
      (agree _ _ (by rfl)) s history)
  rintro t ⟨af, machine, recorded⟩
  have cursor : t = ⟨⟨zeroed s (.low .rbx .W32) af, Image.PeerGet.entry+0xdf⟩,
      history ++ [⟨zeroed s (.low .rbx .W32) af, Image.PeerGet.entry+0xdf⟩]⟩ := by
    cases t; simp_all [Int64.add_assoc]
  rw [cursor]
  have here := agree _ _ (show Image.fetch (Image.PeerGet.entry+0xdf) = some _ from rfl)
  simp only [historySteps, historyStep, instructionStep, here]
  refine ⟨by decide, ?_⟩
  simp [Instr.interp, Operation.interp, RelRegOrMem.interp, ConstExpr.interp, Effects.All,
    Image.PeerGet.entry, List.append_assoc]
  cases af <;> first | exact .inl ⟨rfl, rfl⟩ | exact .inr ⟨rfl, rfl⟩

theorem clear_observed (rxSection : Nat) (s : MachineData) (af : Bool) :
    observeHistory (AllowedipsPeerObservation.edge rxSection)
      [⟨s, Image.PeerGet.entry+0xdd⟩,
       ⟨zeroed s (.low .rbx .W32) af, Image.PeerGet.entry+0xdf⟩,
       ⟨zeroed s (.low .rbx .W32) af, Image.PeerGet.entry+0x9d⟩] = .ok [] := by
  simp [observeHistory, AllowedipsPeerObservation.edge, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]

theorem zeroed_shape (s : MachineData) (af : Bool) :
    (zeroed s (.low .rbx .W32) af).regs = {s.regs with rbx := 0} ∧
    (zeroed s (.low .rbx .W32) af).dmem = s.dmem := by
  simp [zeroed, MachineData.setReg, Reg64s.set, Reg64s.set64]

#print axioms xor32_history
#print axioms clear_history
#print axioms clear_observed
#print axioms zeroed_shape
end Binary.AllowedipsPeerGet
