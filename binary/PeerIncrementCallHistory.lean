import PeerIncrementHistory
import ScanFrame

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- The count write is already present at the next anchored cut. Its
    physical post-state is used as the callback frame base, not as a
    fictitious pre-increment mirror state. -/
theorem increment_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (body : MachineData)
    (coverage : KcovLayout) (preempt : BitVec 32) (ready : CallsReady coverage preempt body)
    (count : body.dmem.loadInt body.regs.r13.toBitVec 4 = some (body.regs.get (.low .rbp .W32)).toNat)
    (countSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange body.regs.r13.toBitVec 4 a)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x44⟩) :
    historySteps fetch 7 (fun t => ∃ af,
      t.machine = ⟨incFinal body af, Image.PeerGet.entry+0x5b⟩ ∧
      ScanTrace (incFinal body af) coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x44⟩, history⟩ := by
  apply historySteps_mono fetch 7 _ _ _ _ (increment_history fetch agree body history count)
  rintro t ⟨af, machine, recorded⟩
  have ready₂ : CallsReady coverage preempt (incFinal body af) := by
    rw [incFinal_shape]
    exact (incremented_ready body coverage preempt ready countSeparate).congr rfl rfl
  have frame := ScanFrame.initial (incFinal body af) coverage preempt ready₂
  refine ⟨af, machine, ScanTrace.of_suffix observed last _ recorded ?_ ?_
    (increment_observed rxSection body af) ?_⟩
  · simpa only [machine] using frame
  · simp [incrementStates, machine]
  · intro q member cut
    rw [increment_cuts body af q member cut]
    exact frame

/-- Execute the real byte-comparison callback after the physical increment.
    The callback's own history and all its actual anchored cuts are retained. -/
theorem increment_call_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (traceByte : TraceConstCmp1Contract fetch)
    (body : MachineData) (coverage : KcovLayout) (preempt : BitVec 32)
    (ready : CallsReady coverage preempt body)
    (count : body.dmem.loadInt body.regs.r13.toBitVec 4 = some (body.regs.get (.low .rbp .W32)).toNat)
    (countSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange body.regs.r13.toBitVec 4 a)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x44⟩) :
    Eventually (historyStep fetch) (fun t => ∃ af,
      t.machine.pc = Image.PeerGet.entry+0x60 ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧
      t.machine.data.regs.rbp = body.regs.rbp ∧
      ScanTrace (incFinal body af) coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x44⟩, history⟩ := by
  have increment := historySteps_eventually fetch 7 _ _
    (increment_trace fetch agree body coverage preempt ready count countSeparate rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ increment
  rintro atCall ⟨af, machine, trace⟩
  have pc : atCall.machine.pc = Image.PeerGet.entry+0x5b := congrArg MachineState.pc machine
  have call := scan_call_cursor fetch "L_ffffffff810f3ec0" atCall
    (by rw [pc]; exact agree _ _ (by rfl)) .constCmp1 traceByte (incFinal body af) coverage preempt trace.frame
    rxSection events trace.observed trace.last (by
      simp [LookupObservation.edge, pc, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ call
  rintro final ⟨pc₂, bx₂, bp₂, trace₂⟩
  have regs := incremented_registers body
  refine ⟨af, by rw [pc₂, pc]; rfl, ?_, ?_, trace.trans trace₂⟩
  · simpa only [machine, incFinal_shape, regs.2.1] using bx₂
  · simpa only [machine, incFinal_shape, regs.2.2.1] using bp₂

#print axioms increment_trace
#print axioms increment_call_history
end Binary.PeerGet
