import PeerLiveGuardsHistory
import PeerFirstStack
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

theorem nonzero_guard_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt body) (accepted : body.regs.get (.low .rbp .W32) ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x3b⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine = ⟨tested (.low .rbp .W32) body af, Image.PeerGet.entry+0x3f⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzZero false t.machine (some ((body.regs.get (.low .rbp .W32)).toNat, 0))]) t)
      ⟨⟨body, Image.PeerGet.entry+0x3b⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (peer_zero_guard fetch agree body history)) last (by
    rintro t ⟨af,machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals rw [frame.stack]; exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨af, machine, recorded⟩
  simp only [beq_iff_eq, accepted, ite_false] at machine recorded
  have nextFrame : ScanFrame base coverage preempt (tested (.low .rbp .W32) body af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, machine, StableTrace.of_observed_suffix observed last _ recorded ?_ ?_ _ ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · simp [machine]
  · rw [machine]
    simp [observeHistory, LookupObservation.edge, LookupObservation.choice,
      Image.Lookup.entry, Image.PeerGet.entry, tested]
    rfl
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

#print axioms nonzero_guard_trace

/-- Accepted live-path guard, retaining its actual TEST flag and decision state. -/
theorem retry_guard_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt body) (accepted : body.regs.get (.low .r15 .W8) ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x60⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine = ⟨tested (.low .r15 .W8) body af, Image.PeerGet.entry+0x69⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzRetry false t.machine]) t)
      ⟨⟨body, Image.PeerGet.entry+0x60⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (peer_retry_guard fetch agree body history)) last (by
    rintro t ⟨af,machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals rw [frame.stack]; exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨af, machine, recorded⟩
  simp only [beq_iff_eq, accepted, ite_false] at machine recorded
  have nextFrame : ScanFrame base coverage preempt (tested (.low .r15 .W8) body af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, machine, StableTrace.of_observed_suffix observed last _ recorded ?_ ?_ _ ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · simp [machine]
  · rw [machine]
    simp [observeHistory, LookupObservation.edge, LookupObservation.choice,
      Image.Lookup.entry, Image.PeerGet.entry, tested]
    rfl
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

#print axioms retry_guard_trace

/-- Accepted live-path guard, retaining its actual TEST flag and decision state. -/
theorem negative_guard_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt body) (accepted : (body.regs.get (.low .rbp .W32)).msb = false)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x77⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine = ⟨tested (.low .rbp .W32) body af, Image.PeerGet.entry+0x7b⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzNegative false t.machine]) t)
      ⟨⟨body, Image.PeerGet.entry+0x77⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (peer_negative_guard fetch agree body history)) last (by
    rintro t ⟨af,machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals rw [frame.stack]; exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨af, machine, recorded⟩
  simp only [accepted, Bool.false_eq_true, ite_false] at machine recorded
  have nextFrame : ScanFrame base coverage preempt (tested (.low .rbp .W32) body af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, machine, StableTrace.of_observed_suffix observed last _ recorded ?_ ?_ _ ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · simp [machine]
  · rw [machine]
    simp [observeHistory, LookupObservation.edge, LookupObservation.choice,
      Image.Lookup.entry, Image.PeerGet.entry, tested]
    rfl
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

#print axioms negative_guard_trace

/-- Accepted live-path guard, retaining its actual TEST flag and decision state. -/
theorem wrap_guard_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (safe : CallStackSafe outer base.regs.rsp)
    (frame : ScanFrame base coverage preempt body) (accepted : (body.regs.get (.low .r12 .W32)).msb = false)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x8a⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun t => ∃ af,
      t.machine = ⟨tested (.low .r12 .W32) body af, Image.PeerGet.entry+0x8f⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzWraps false t.machine]) t)
      ⟨⟨body, Image.PeerGet.entry+0x8a⟩, history⟩ := by
  have guarded := history_guard_suffix (guard := StackGuard outer)
      (historySteps_eventually fetch 2 _ _ (peer_wrap_guard fetch agree body history)) last (by
    rintro t ⟨af,machine,recorded⟩
    refine ⟨_,recorded,?_⟩
    intro q member
    simp only [List.dropLast_cons_cons,List.dropLast_singleton,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    all_goals change body.regs.rsp≠outer+8
    all_goals rw [frame.stack]; exact safe.1)
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ guarded
  rintro t ⟨af, machine, recorded⟩
  simp only [accepted, Bool.false_eq_true, ite_false] at machine recorded
  have nextFrame : ScanFrame base coverage preempt (tested (.low .r12 .W32) body af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, machine, StableTrace.of_observed_suffix observed last _ recorded ?_ ?_ _ ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · simp [machine]
  · rw [machine]
    simp [observeHistory, LookupObservation.edge, LookupObservation.choice,
      Image.Lookup.entry, Image.PeerGet.entry, tested]
    rfl
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame

#print axioms wrap_guard_trace

end Binary.PeerGet.First
