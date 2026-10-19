import PeerLiveSetupHistory
import PeerFirstLiveGuards
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

theorem live_negative_arguments_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x6e⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine = ⟨xorMoved body (.low .rdi .W32) (.low .rsi .W32) (.low .rbp .W32) af,
        Image.PeerGet.entry+0x72⟩ ∧
      StableTrace base coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x6e⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (negative_arguments_history fetch agree body history)) last (by
    rintro t ⟨af,machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals rw [frame.stack]; exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨af, machine, recorded⟩
  have first : ScanFrame base coverage preempt (zeroed body (.low .rdi .W32) af) := by
    apply frame.congr <;> rfl
  have second : ScanFrame base coverage preempt
      (xorMoved body (.low .rdi .W32) (.low .rsi .W32) (.low .rbp .W32) af) := by
    apply frame.congr <;> rfl
  rw [machine] at recorded
  refine ⟨af, machine, StableTrace.of_suffix observed last _ recorded ?_ ?_ ?_ ?_⟩
  · simpa only [machine] using second
  · simp [machine]
  · simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact first
    · exact second

theorem live_wrap_arguments_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x80⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine = ⟨xorMoved body (.low .rdi .W32) (.low .rsi .W32) (.low .r12 .W32) af,
        Image.PeerGet.entry+0x85⟩ ∧
      StableTrace base coverage preempt rxSection history events t)
      ⟨⟨body, Image.PeerGet.entry+0x80⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (wrap_arguments_history fetch agree body history)) last (by
    rintro t ⟨af,machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals rw [frame.stack]; exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨af, machine, recorded⟩
  have first : ScanFrame base coverage preempt (zeroed body (.low .rdi .W32) af) := by
    apply frame.congr <;> rfl
  have second : ScanFrame base coverage preempt
      (xorMoved body (.low .rdi .W32) (.low .rsi .W32) (.low .r12 .W32) af) := by
    apply frame.congr <;> rfl
  rw [machine] at recorded
  refine ⟨af, machine, StableTrace.of_suffix observed last _ recorded ?_ ?_ ?_ ?_⟩
  · simpa only [machine] using second
  · simp [machine]
  · simp [observeHistory, LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact first
    · exact second


/-- The nonzero count makes the folded result decision false, at the MOV's
    actual successor before XOR and the comparison callback. -/
theorem live_result_arguments_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt body)
    (nonzero : body.regs.get (.low .rbp .W32) ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x94⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine = ⟨zeroed (body.setReg (.low .rsi .W32) (body.regs.get (.low .rbp .W32)))
        (.low .rdi .W32) af, Image.PeerGet.entry+0x98⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroDead false
          ⟨body.setReg (.low .rsi .W32) (body.regs.get (.low .rbp .W32)), Image.PeerGet.entry+0x96⟩]) t)
      ⟨⟨body, Image.PeerGet.entry+0x94⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (live_result_arguments_history fetch agree body history)) last (by
    rintro t ⟨af,machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals rw [frame.stack]; exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨af, machine, recorded⟩
  have first : ScanFrame base coverage preempt (body.setReg (.low .rsi .W32) (body.regs.get (.low .rbp .W32))) := by
    apply frame.congr <;> rfl
  have second : ScanFrame base coverage preempt
      (zeroed (body.setReg (.low .rsi .W32) (body.regs.get (.low .rbp .W32))) (.low .rdi .W32) af) := by
    apply frame.congr <;> rfl
  rw [machine] at recorded
  refine ⟨af, machine, StableTrace.of_observed_suffix observed last _ recorded ?_ ?_ _ ?_ ?_⟩
  · simpa only [machine] using second
  · simp [machine]
  · have h : (body.regs.get (.low .rbp .W32) == 0) = false := by
      apply Bool.eq_false_iff.mpr
      intro h
      exact nonzero (beq_iff_eq.mp h)
    simpa only [h] using live_result_observed rxSection body af
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact first
    · exact second

#print axioms live_negative_arguments_trace
#print axioms live_wrap_arguments_trace
#print axioms live_result_arguments_trace
end Binary.PeerGet.First
