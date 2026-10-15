import PeerDeadSetup

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- Actual callback/setup/callback stage on the zero-count branch. -/
theorem dead_negative_stage (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (base body : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xb0⟩) :
    Eventually (historyStep fetch) (fun t => ∃ point : MachineState,
      t.machine.pc = Image.PeerGet.entry+0xbe ∧
      EqualOutside (scanWrites base coverage) base.dmem point.data.dmem ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzNegative false point]) t)
      ⟨⟨body, Image.PeerGet.entry+0xb0⟩, history⟩ := by
  have first := scan_call_cursor fetch "L_ffffffff810f3100"
    ⟨⟨body, Image.PeerGet.entry+0xb0⟩, history⟩ (agree _ _ (by rfl)) .pc tracePc
    base coverage preempt frame (frame).ready.pc_allowed
    rxSection events observed last (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro afterPc ⟨pc₁, _, _, trace₁⟩
  change afterPc.machine.pc = Image.PeerGet.entry+0xb5 at pc₁
  have setup := historySteps_eventually fetch 2 _ _
    (dead_negative_trace fetch agree base afterPc.machine.data coverage preempt trace₁.frame
      rxSection afterPc.history events trace₁.observed (by rw [← pc₁]; exact trace₁.last))
  have cursor : (⟨⟨afterPc.machine.data, Image.PeerGet.entry+0xb5⟩, afterPc.history⟩ : Executed) = afterPc := by
    rw [← pc₁]
  rw [cursor] at setup
  apply eventually_trans (historyStep fetch) _ _ _ setup
  rintro afterSetup ⟨af₁, af₂, machine₂, trace₂⟩
  let point : MachineState := ⟨zeroed afterPc.machine.data (.low .rsi .W32) af₁, Image.PeerGet.entry+0xb7⟩
  have pc₂ : afterSetup.machine.pc = Image.PeerGet.entry+0xb9 := congrArg MachineState.pc machine₂
  have final := scan_call_cursor fetch "L_ffffffff810f3f00" afterSetup
    (by rw [pc₂]; exact agree _ _ (by rfl)) .constCmp4 traceCmp base coverage preempt trace₂.frame (LookupCoverage.compare_allowed comparison (by decide))
    rxSection (events ++ [LookupObservation.decision rxSection .refcountAddNzNegative false point])
    trace₂.observed trace₂.last (by
      simp [LookupObservation.edge, pc₂, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ final
  rintro t ⟨pc₃, _, _, trace₃⟩
  refine ⟨point, ?_, trace₁.frame.memory, trace₁.trans (trace₂.trans trace₃)⟩
  rw [pc₃, pc₂]
  rfl

#print axioms dead_negative_stage

/-- Actual callback/setup/callback stage on the zero-count branch. -/
theorem dead_wrap_stage (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (base body : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xbe⟩) :
    Eventually (historyStep fetch) (fun t => ∃ point : MachineState,
      t.machine.pc = Image.PeerGet.entry+0xcf ∧
      EqualOutside (scanWrites base coverage) base.dmem point.data.dmem ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzWraps false point]) t)
      ⟨⟨body, Image.PeerGet.entry+0xbe⟩, history⟩ := by
  have first := scan_call_cursor fetch "L_ffffffff810f3100"
    ⟨⟨body, Image.PeerGet.entry+0xbe⟩, history⟩ (agree _ _ (by rfl)) .pc tracePc
    base coverage preempt frame (frame).ready.pc_allowed
    rxSection events observed last (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro afterPc ⟨pc₁, _, _, trace₁⟩
  change afterPc.machine.pc = Image.PeerGet.entry+0xc3 at pc₁
  have setup := historySteps_eventually fetch 2 _ _
    (dead_wrap_trace fetch agree base afterPc.machine.data coverage preempt trace₁.frame
      rxSection afterPc.history events trace₁.observed (by rw [← pc₁]; exact trace₁.last))
  have cursor : (⟨⟨afterPc.machine.data, Image.PeerGet.entry+0xc3⟩, afterPc.history⟩ : Executed) = afterPc := by
    rw [← pc₁]
  rw [cursor] at setup
  apply eventually_trans (historyStep fetch) _ _ _ setup
  rintro afterSetup ⟨af, machine₂, trace₂⟩
  let point : MachineState := ⟨oneArgument afterPc.machine.data, Image.PeerGet.entry+0xc8⟩
  have pc₂ : afterSetup.machine.pc = Image.PeerGet.entry+0xca := congrArg MachineState.pc machine₂
  have final := scan_call_cursor fetch "L_ffffffff810f3f00" afterSetup
    (by rw [pc₂]; exact agree _ _ (by rfl)) .constCmp4 traceCmp base coverage preempt trace₂.frame (LookupCoverage.compare_allowed comparison (by decide))
    rxSection (events ++ [LookupObservation.decision rxSection .refcountAddNzWraps false point])
    trace₂.observed trace₂.last (by
      simp [LookupObservation.edge, pc₂, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ final
  rintro t ⟨pc₃, _, _, trace₃⟩
  refine ⟨point, ?_, trace₁.frame.memory, trace₁.trans (trace₂.trans trace₃)⟩
  rw [pc₃, pc₂]
  rfl

#print axioms dead_wrap_stage

/-- Actual callback/setup/callback stage on the zero-count branch. -/
theorem dead_result_stage (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (base body : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xcf⟩) :
    Eventually (historyStep fetch) (fun t => ∃ point : MachineState,
      t.machine.pc = Image.PeerGet.entry+0xdd ∧
      EqualOutside (scanWrites base coverage) base.dmem point.data.dmem ∧
      ScanTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroDead true point]) t)
      ⟨⟨body, Image.PeerGet.entry+0xcf⟩, history⟩ := by
  have first := scan_call_cursor fetch "L_ffffffff810f3100"
    ⟨⟨body, Image.PeerGet.entry+0xcf⟩, history⟩ (agree _ _ (by rfl)) .pc tracePc
    base coverage preempt frame (frame).ready.pc_allowed
    rxSection events observed last (by
      simp [LookupObservation.edge, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_trans (historyStep fetch) _ _ _ first
  rintro afterPc ⟨pc₁, _, _, trace₁⟩
  change afterPc.machine.pc = Image.PeerGet.entry+0xd4 at pc₁
  have setup := historySteps_eventually fetch 2 _ _
    (dead_result_trace fetch agree base afterPc.machine.data coverage preempt trace₁.frame
      rxSection afterPc.history events trace₁.observed (by rw [← pc₁]; exact trace₁.last))
  have cursor : (⟨⟨afterPc.machine.data, Image.PeerGet.entry+0xd4⟩, afterPc.history⟩ : Executed) = afterPc := by
    rw [← pc₁]
  rw [cursor] at setup
  apply eventually_trans (historyStep fetch) _ _ _ setup
  rintro afterSetup ⟨af₁, af₂, machine₂, trace₂⟩
  let point : MachineState := ⟨zeroed afterPc.machine.data (.low .rsi .W32) af₁, Image.PeerGet.entry+0xd6⟩
  have pc₂ : afterSetup.machine.pc = Image.PeerGet.entry+0xd8 := congrArg MachineState.pc machine₂
  have final := scan_call_cursor fetch "L_ffffffff810f3f00" afterSetup
    (by rw [pc₂]; exact agree _ _ (by rfl)) .constCmp4 traceCmp base coverage preempt trace₂.frame (LookupCoverage.compare_allowed comparison (by decide))
    rxSection (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroDead true point])
    trace₂.observed trace₂.last (by
      simp [LookupObservation.edge, pc₂, Image.Lookup.entry, Image.PeerGet.entry]; rfl)
  apply eventually_weaken (historyStep fetch) _ _ _ _ final
  rintro t ⟨pc₃, _, _, trace₃⟩
  refine ⟨point, ?_, trace₁.frame.memory, trace₁.trans (trace₂.trans trace₃)⟩
  rw [pc₃, pc₂]
  rfl

#print axioms dead_result_stage

/-- All six callbacks and all three folded decisions, from the zero guard's
    taken edge to the shared clear branch. Every point and cut is actual. -/
theorem dead_callbacks_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (body : MachineData) (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt body)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xb0⟩) :
    Eventually (historyStep fetch) (fun t => ∃ negative wrap dead : MachineState,
      t.machine.pc = Image.PeerGet.entry+0xdd ∧
      EqualOutside (scanWrites body coverage) body.dmem negative.data.dmem ∧
      EqualOutside (scanWrites body coverage) body.dmem wrap.data.dmem ∧
      EqualOutside (scanWrites body coverage) body.dmem dead.data.dmem ∧
      ScanTrace body coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzNegative false negative,
          LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
          LookupObservation.decision rxSection .peerGetMaybeZeroDead true dead]) t)
      ⟨⟨body, Image.PeerGet.entry+0xb0⟩, history⟩ := by
  have negative := dead_negative_stage fetch agree tracePc traceCmp body body coverage preempt
    (ScanFrame.initial body coverage preempt ready) comparison rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ negative
  rintro first ⟨negative, pc₁, negativeFrame, trace₁⟩
  let events₁ := events ++ [LookupObservation.decision rxSection .refcountAddNzNegative false negative]
  have wrap := dead_wrap_stage fetch agree tracePc traceCmp body first.machine.data coverage preempt
    trace₁.frame comparison rxSection first.history events₁ trace₁.observed (by rw [← pc₁]; exact trace₁.last)
  have cursor₁ : (⟨⟨first.machine.data, Image.PeerGet.entry+0xbe⟩, first.history⟩ : Executed) = first := by rw [← pc₁]
  rw [cursor₁] at wrap
  apply eventually_trans (historyStep fetch) _ _ _ wrap
  rintro second ⟨wrap, pc₂, wrapFrame, trace₂⟩
  let events₂ := events₁ ++ [LookupObservation.decision rxSection .refcountAddNzWraps false wrap]
  have dead := dead_result_stage fetch agree tracePc traceCmp body second.machine.data coverage preempt
    trace₂.frame comparison rxSection second.history events₂ trace₂.observed (by rw [← pc₂]; exact trace₂.last)
  have cursor₂ : (⟨⟨second.machine.data, Image.PeerGet.entry+0xcf⟩, second.history⟩ : Executed) = second := by rw [← pc₂]
  rw [cursor₂] at dead
  apply eventually_weaken (historyStep fetch) _ _ _ _ dead
  rintro final ⟨dead, pc₃, deadFrame, trace₃⟩
  refine ⟨negative, wrap, dead, pc₃, negativeFrame, wrapFrame, deadFrame, ?_⟩
  simpa only [events₁, events₂, List.append_assoc, List.cons_append, List.nil_append] using
    trace₁.trans (trace₂.trans trace₃)

#print axioms dead_callbacks_history
end Binary.PeerGet
