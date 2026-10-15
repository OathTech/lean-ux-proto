import HistoryRegions

namespace Binary.LookupHistory
local instance : Labels := Image.linkedLabels

/-- TEST/JS records the actual undefined AF in both successor states. -/
theorem test_self_sign (fetch : Int64 → Option Decoded) (pc : Int64)
    (w : Width) (r : Reg w) (target : Label) (testSize jumpSize : Nat)
    (testPositive : 0 < testSize) (jumpPositive : 0 < jumpSize)
    (first : fetch pc = some ⟨.regular .W64 w (.test (.reg r) (.reg r)), testSize⟩)
    (second : fetch (pc + .ofNat testSize) =
      some ⟨.regular .W64 .W64 (.jcc .s target), jumpSize⟩)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory r s (pc + .ofNat testSize)
      (if (s.regs.get r).msb then label target else pc + .ofNat testSize + .ofNat jumpSize) history)
      ⟨⟨s, pc⟩, history⟩ := by
  unfold TestHistory
  simp only [historySteps, historyStep, instructionStep, first, second,
    Instr.interp, Operation.interp, RegOrMem.interp, Operand.interp, Effects.All]
  refine ⟨testPositive, fun af => ⟨jumpPositive, ?_⟩⟩
  simp only [StatusFlags.from_result, CondCode.interp, BitVec.and_self]
  cases hz : (s.regs.get r).msb <;>
    simp_all [Effects.All, tested, StatusFlags.from_result, List.append_assoc]

theorem peer_negative_guard (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .rbp .W32) s (Image.PeerGet.entry+0x79)
      (if (s.regs.get (.low .rbp .W32)).msb then Image.PeerGet.entry+0xe1
       else Image.PeerGet.entry+0x7b) history)
      ⟨⟨s, Image.PeerGet.entry+0x77⟩, history⟩ := by
  exact test_self_sign fetch _ _ _ "L_ffffffff813996f1" 2 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

theorem peer_wrap_guard (fetch : Int64 → Option Decoded)
    (agree : ∀ p i, Image.fetch p = some i → fetch p = some i)
    (s : MachineData) (history : List MachineState) :
    historySteps fetch 2 (TestHistory (.low .r12 .W32) s (Image.PeerGet.entry+0x8d)
      (if (s.regs.get (.low .r12 .W32)).msb then Image.PeerGet.entry+0xe1
       else Image.PeerGet.entry+0x8f) history)
      ⟨⟨s, Image.PeerGet.entry+0x8a⟩, history⟩ := by
  exact test_self_sign fetch _ _ _ "L_ffffffff813996f1" 3 2 (by decide) (by decide)
    (agree _ _ (by rfl)) (agree _ _ (by rfl)) s history

#print axioms test_self_sign
#print axioms peer_negative_guard
#print axioms peer_wrap_guard
end Binary.LookupHistory
