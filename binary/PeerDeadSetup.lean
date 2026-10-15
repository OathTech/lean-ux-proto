import PeerCompareHistory
import ScanFrame

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- The compiler-folded negative decision belongs to the first XOR's
    actual successor, before the next XOR and the instrumentation CALL. -/
theorem dead_negative_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xb5⟩) :
    historySteps fetch 2 (fun t => ∃ af₁ af₂,
      t.machine = ⟨zeroed (zeroed body (.low .rsi .W32) af₁) (.low .rdi .W32) af₂,
        Image.PeerGet.entry+0xb9⟩ ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzNegative false
          ⟨zeroed body (.low .rsi .W32) af₁, Image.PeerGet.entry+0xb7⟩]) t)
      ⟨⟨body, Image.PeerGet.entry+0xb5⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (dead_negative_arguments_history fetch agree body history)
  rintro t ⟨af₁, af₂, machine, recorded⟩
  have firstFrame : ScanFrame base coverage preempt (zeroed body (.low .rsi .W32) af₁) := by
    apply frame.congr <;> rfl
  have secondFrame : ScanFrame base coverage preempt
      (zeroed (zeroed body (.low .rsi .W32) af₁) (.low .rdi .W32) af₂) := by
    apply firstFrame.congr <;> rfl
  rw [machine] at recorded
  refine ⟨af₁, af₂, machine,
    ScanTrace.of_observed_suffix observed last _ recorded ?_ ?_ _
      (dead_negative_observed rxSection body af₁ af₂) ?_⟩
  · simpa only [machine] using secondFrame
  · simp [machine]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact firstFrame
    · exact secondFrame

#print axioms dead_negative_trace

/-- The compiler-folded result decision belongs to the first XOR's
    actual successor, before the next XOR and the instrumentation CALL. -/
theorem dead_result_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xd4⟩) :
    historySteps fetch 2 (fun t => ∃ af₁ af₂,
      t.machine = ⟨zeroed (zeroed body (.low .rsi .W32) af₁) (.low .rdi .W32) af₂,
        Image.PeerGet.entry+0xd8⟩ ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroDead true
          ⟨zeroed body (.low .rsi .W32) af₁, Image.PeerGet.entry+0xd6⟩]) t)
      ⟨⟨body, Image.PeerGet.entry+0xd4⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (dead_result_arguments_history fetch agree body history)
  rintro t ⟨af₁, af₂, machine, recorded⟩
  have firstFrame : ScanFrame base coverage preempt (zeroed body (.low .rsi .W32) af₁) := by
    apply frame.congr <;> rfl
  have secondFrame : ScanFrame base coverage preempt
      (zeroed (zeroed body (.low .rsi .W32) af₁) (.low .rdi .W32) af₂) := by
    apply firstFrame.congr <;> rfl
  rw [machine] at recorded
  refine ⟨af₁, af₂, machine,
    ScanTrace.of_observed_suffix observed last _ recorded ?_ ?_ _
      (dead_result_observed rxSection body af₁ af₂) ?_⟩
  · simpa only [machine] using secondFrame
  · simp [machine]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact firstFrame
    · exact secondFrame

#print axioms dead_result_trace

theorem dead_wrap_trace (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : KcovLayout) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xc3⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨zeroed (oneArgument body) (.low .rdi .W32) af, Image.PeerGet.entry+0xca⟩ ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzWraps false
          ⟨oneArgument body, Image.PeerGet.entry+0xc8⟩]) t)
      ⟨⟨body, Image.PeerGet.entry+0xc3⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (dead_wrap_arguments_history fetch agree body history)
  rintro t ⟨af, machine, recorded⟩
  have firstFrame : ScanFrame base coverage preempt (oneArgument body) := by
    apply frame.congr <;> rfl
  have secondFrame : ScanFrame base coverage preempt (zeroed (oneArgument body) (.low .rdi .W32) af) := by
    apply firstFrame.congr <;> rfl
  rw [machine] at recorded
  refine ⟨af, machine, ScanTrace.of_observed_suffix observed last _ recorded ?_ ?_ _
    (dead_wrap_observed rxSection body af) ?_⟩
  · simpa only [machine] using secondFrame
  · simp [machine]
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact firstFrame
    · exact secondFrame

#print axioms dead_wrap_trace
end Binary.PeerGet
