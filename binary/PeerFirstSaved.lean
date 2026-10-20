import PeerSavedHistory
import PeerFirstStack
namespace Binary.PeerGet.First
open Callback
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

theorem return_from_saved_history (fetch : Int64 → Option Decoded)
    (agree : TrustBase.AnchoredDecoderAgreement fetch)
    (initial : MachineState) (safe : StackSlots outer initial.data.regs.rsp) (body : MachineData) (returnAddress : UInt64)
    (history : List MachineState)
    (entry : TrustBase.EntryFrame initial returnAddress)
    (sp : body.regs.rsp = initial.data.regs.rsp - 48)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (separate : ∀ address, InRange (initial.data.regs.rsp.toBitVec - 48) 56 address →
      ¬writes address)
    (last : history.getLast?=some ⟨body,Image.PeerGet.entry+0xa2⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun final =>
      TrustBase.Returned initial final.machine returnAddress ∧
      final.machine.data.regs.rax = body.regs.rbx ∧
      final.machine.data.dmem = body.dmem ∧
      final.history = history ++ restoreStates body initial.data.regs.rbx initial.data.regs.rbp
        initial.data.regs.r12 initial.data.regs.r13 initial.data.regs.r14 initial.data.regs.r15 returnAddress)
      ⟨⟨body, Image.PeerGet.entry+0xa2⟩, history⟩ := by
  apply history_guard_suffix
    (historySteps_eventually fetch 8 _ _ (PeerGet.return_from_saved_history fetch agree initial body
      returnAddress history entry sp writes frame separate)) last
  rintro t ⟨_,_,_,recorded⟩
  refine ⟨_,recorded,?_⟩
  intro q member
  simp only [restoreStates,List.dropLast_cons_cons,List.dropLast_singleton,
    List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals change _ ≠ outer+8
  all_goals simp only [restoreData]
  all_goals rw [sp]; slots_guard safe

#print axioms return_from_saved_history
end Binary.PeerGet.First
