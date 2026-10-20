import HistoryGuard
import CallHistory

namespace Binary.Instrumentation.First
open TrustBase Callback
local instance : Labels := Image.linkedLabels

/-- Compose the actual CALL with a proved service execution. The service's
history/observation postcondition is arbitrary and retained unchanged. The
physical argument (ABI stack cancellation, return-slot readability and write
footprint) is independent of the coverage or observation context. -/
theorem call_return (fetch : Int64 → Option Decoded) (pc : Int64) (target : Label)
    (here : fetch pc = some ⟨callInstruction target, 5⟩)
    (s : MachineData) (history : List MachineState)
    (outer : UInt64) (outside : s.regs.rsp≠outer+8)
    (writes : BitVec 64 → Prop) (State : Mem 64 → Prop) (Q : Executed → Prop)
    (mapped : (s.dmem.loadInt (s.regs.rsp.toBitVec-8) 8).isSome = true)
    (separate : ∀ a, writes a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a)
    (service : Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      Returned (calledState s (pc+5) (label target)) t.machine (pc+5).toUInt64 ∧
      State t.machine.data.dmem ∧
      EqualOutside writes (calledState s (pc+5) (label target)).data.dmem t.machine.data.dmem ∧ Q t)
      ⟨calledState s (pc+5) (label target), history ++ [calledState s (pc+5) (label target)]⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t =>
      Returned (calledState s (pc+5) (label target)) t.machine (pc+5).toUInt64 ∧
      State t.machine.data.dmem ∧ t.machine.data.regs.rsp = s.regs.rsp ∧
      (t.machine.data.dmem.loadInt (t.machine.data.regs.rsp.toBitVec-8) 8).isSome = true ∧
      EqualOutside (fun a => InRange (s.regs.rsp.toBitVec-8) 8 a ∨ writes a)
        s.dmem t.machine.data.dmem ∧ Q t) ⟨⟨s, pc⟩, history⟩ := by
  have first : Eventually (guardedHistoryStep fetch (StackGuard outer))
      (fun t => t.machine=calledState s (pc+5) (label target) ∧
        t.history=history++[t.machine]) ⟨⟨s,pc⟩,history⟩ := by
    apply step_cps
    refine ⟨outside,?_⟩
    exact instruction_mono fetch _ _ _ (fun next h => .done _ h)
      (call_instruction fetch pc target here s history mapped)
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ first
  rintro entered ⟨machine, recorded⟩
  have cursor : entered = ⟨calledState s (pc+5) (label target),
      history ++ [calledState s (pc+5) (label target)]⟩ := by
    cases entered; simp_all
  rw [cursor]
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ service
  rintro final ⟨returned, state, frame, rest⟩
  have sp := (returned_caller s (pc+5) (label target) final.machine returned).2.1
  have word : final.machine.data.dmem.loadInt (s.regs.rsp.toBitVec-8) 8 =
      some ((pc+5).toBitVec.toNat : Int) := by
    have same := frame.loadInt (s.regs.rsp.toBitVec-8) 8 (by
      intro byte bound written
      exact separate _ written ⟨byte, bound, rfl⟩)
    exact same.symm.trans (load64_store s.dmem (s.regs.rsp.toBitVec-8) (pc+5).toBitVec)
  exact ⟨returned, state, sp, by rw [sp, word]; rfl,
    (storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 (pc+5).toBitVec.toInt).trans frame, rest⟩

end Binary.Instrumentation.First
