import PeerIncrementCallHistory
import FirstScanFrame
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

/-- The count write is already present at the next anchored cut. Its
    physical post-state is used as the callback frame base, not as a
    fictitious pre-increment mirror state. -/
theorem increment_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (body : MachineData) (safe : CallStackSafe outer body.regs.rsp)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32) (ready : LookupCoverage.CallsReady coverage preempt body)
    (count : body.dmem.loadInt body.regs.r13.toBitVec 4 = some (body.regs.get (.low .rbp .W32)).toNat)
    (countSeparate : ∀ a, LookupCoverage.Context.bytes coverage a → ¬InRange body.regs.r13.toBitVec 4 a)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x44⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine = ⟨incFinal body af, Image.PeerGet.entry+0x5b⟩ ∧
      t.history = history ++ incrementStates body af ∧
      ScanTrace (incFinal body af) coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x44⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 7 _ _ (increment_history fetch agree body history count)) last (by
    rintro t ⟨af, machine, recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [incrementStates,List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨af, machine, recorded⟩
  have ready₂ : LookupCoverage.CallsReady coverage preempt (incFinal body af) := by
    rw [incFinal_shape]
    exact (incremented_lookup_ready body coverage preempt ready countSeparate).congr rfl rfl
  have frame := ScanFrame.initial (incFinal body af) coverage preempt ready₂
  refine ⟨af, machine, recorded, ScanTrace.of_suffix observed last _ recorded ?_ ?_
    (increment_observed rxSection body af) ?_⟩
  · simpa only [machine] using frame
  · simp [incrementStates, machine]
  · intro q member cut
    rw [increment_cuts body af q member cut]
    exact frame

/-- Execute the real byte-comparison callback after the physical increment.
    The callback's own history and all its actual anchored cuts are retained. -/
theorem increment_call_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (traceByte : LeafService fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1))
    (body : MachineData) (safe : CallStackSafe outer body.regs.rsp) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt body)
    (count : body.dmem.loadInt body.regs.r13.toBitVec 4 = some (body.regs.get (.low .rbp .W32)).toNat)
    (countSeparate : ∀ a, LookupCoverage.Context.bytes coverage a → ¬InRange body.regs.r13.toBitVec 4 a)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x44⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine.pc = Image.PeerGet.entry+0x60 ∧
      t.machine.data.regs.rbx = body.regs.rbx ∧
      t.machine.data.regs.rbp = body.regs.rbp ∧
      ScanTrace (incFinal body af) coverage preempt rxSection history events t ∧
      PeerCountPhase.StableExtension (history ++ incrementStates body af) t.history)
      ⟨⟨body, Image.PeerGet.entry+0x44⟩, history⟩ := by
  have increment := increment_trace fetch agree body safe coverage preempt ready count countSeparate rxSection history events observed last
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ increment
  rintro atCall ⟨af, machine, recorded, trace⟩
  have pc : atCall.machine.pc = Image.PeerGet.entry+0x5b := congrArg MachineState.pc machine
  have call := scan_call_cursor fetch "L_ffffffff810f3ec0" atCall
    (by rw [pc]; exact agree _ _ (by rfl)) .constCmp1 traceByte (incFinal body af) coverage preempt safe trace.frame (LookupCoverage.compare_allowed comparison (by decide))
    rxSection events trace.observed trace.last (by
      simp [LookupObservation.edge, pc, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ call
  rintro final ⟨pc₂, bx₂, bp₂, trace₂⟩
  have regs := incremented_registers body
  refine ⟨af, by rw [pc₂, pc]; rfl, ?_, ?_, trace.trans trace₂.toSegmentTrace, by simpa only [recorded] using trace₂.stable⟩
  · simpa only [machine, incFinal_shape, regs.2.1] using bx₂
  · simpa only [machine, incFinal_shape, regs.2.2.1] using bp₂

#print axioms increment_trace
#print axioms increment_call_history
end Binary.PeerGet.First
