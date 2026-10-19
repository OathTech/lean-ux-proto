import HistoryGuard
import LookupPrologueHistory

namespace Binary.Lookup.First
open Callback
local instance : Labels := Image.linkedLabels

/-- Strengthen the existing ten-instruction history without redoing its
memory calculations. The endpoint is the first coverage callback entry. -/
theorem prologue (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch) (s : MachineData)
    (history : List MachineState)
    (last : history.getLast?=some ⟨s,Image.Lookup.entry⟩)
    (mapped : ∀ n < 6,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome=true) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp))
      (fun t => t.machine=prologueCalled s ∧
        t.history=history++(prologueStates s++[prologueCalled s]))
      ⟨⟨s,Image.Lookup.entry⟩,history⟩ := by
  apply history_guard_suffix
    (historySteps_eventually fetch 10 _ _ (prologue_history fetch agree s history mapped)) last
  rintro t ⟨_,recorded⟩
  refine ⟨prologueStates s++[prologueCalled s],recorded,?_⟩
  intro q member
  simp only [prologueStates,List.cons_append,List.nil_append,List.dropLast_cons_cons,
    List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    change _ ≠ s.regs.rsp+8
  all_goals simp only [prologueData,savedCount]
  all_goals stack_not_return

#print axioms prologue
end Binary.Lookup.First
