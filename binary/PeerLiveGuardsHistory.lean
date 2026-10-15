import PeerSignHistory
import ScanFrame

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- Accepted live-path guard, retaining its actual TEST flag and decision state. -/
theorem nonzero_guard_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body) (accepted : body.regs.get (.low .rbp .W32) ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x3b⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨tested (.low .rbp .W32) body af, Image.PeerGet.entry+0x3f⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzZero false t.machine (some ((body.regs.get (.low .rbp .W32)).toNat, 0))]) t)
      ⟨⟨body, Image.PeerGet.entry+0x3b⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (peer_zero_guard fetch agree body history)
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
    (frame : ScanFrame base coverage preempt body) (accepted : body.regs.get (.low .r15 .W8) ≠ 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x60⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨tested (.low .r15 .W8) body af, Image.PeerGet.entry+0x69⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzRetry false t.machine]) t)
      ⟨⟨body, Image.PeerGet.entry+0x60⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (peer_retry_guard fetch agree body history)
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
    (frame : ScanFrame base coverage preempt body) (accepted : (body.regs.get (.low .rbp .W32)).msb = false)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x77⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨tested (.low .rbp .W32) body af, Image.PeerGet.entry+0x7b⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzNegative false t.machine]) t)
      ⟨⟨body, Image.PeerGet.entry+0x77⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (peer_negative_guard fetch agree body history)
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
    (frame : ScanFrame base coverage preempt body) (accepted : (body.regs.get (.low .r12 .W32)).msb = false)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x8a⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨tested (.low .r12 .W32) body af, Image.PeerGet.entry+0x8f⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzWraps false t.machine]) t)
      ⟨⟨body, Image.PeerGet.entry+0x8a⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (peer_wrap_guard fetch agree body history)
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

end Binary.PeerGet
