import PeerLiveEntryHistory
import AllowedipsPeerCoverageHistory
import AllowedipsPeerDeadSuffixHistory

namespace Binary.AllowedipsPeerGet
open PeerGet LookupHistory AllowedipsPeerHistory
open TrustBase LookupHistory AllowedipsPeerHistory
local instance : Labels := Image.linkedLabels

/-- The actual zero guard, including its comparison operands (0, 0).
    Zero-count peers remain in scope without an added liveness premise. -/
theorem zero_guard_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (base body : MachineData)
    (coverage : AllowedipsPeerCoverage.Context) (preempt : BitVec 32)
    (frame : ScanFrame base coverage preempt body) (zero : body.regs.get (.low .rbp .W32) = 0)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsPeerObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x3b⟩) :
    historySteps fetch 2 (fun t => ∃ af,
      t.machine = ⟨tested (.low .rbp .W32) body af, Image.PeerGet.entry+0xb0⟩ ∧
      StableTrace base coverage preempt rxSection history
        (events ++ [LookupObservation.decision rxSection .refcountAddNzZero true t.machine (some (0, 0))]) t)
      ⟨⟨body, Image.PeerGet.entry+0x3b⟩, history⟩ := by
  apply historySteps_mono fetch 2 _ _ _ _ (peer_zero_guard fetch agree body history)
  rintro t ⟨af, machine, recorded⟩
  simp only [zero, BEq.rfl, ite_true] at machine recorded
  have nextFrame : ScanFrame base coverage preempt (tested (.low .rbp .W32) body af) :=
    frame.congr rfl rfl rfl rfl rfl rfl
  refine ⟨af, machine, StableTrace.of_observed_suffix observed last _ recorded ?_ ?_ _ ?_ ?_⟩
  · simpa only [machine] using nextFrame
  · simp [machine]
  · rw [machine]
    simp [observeHistory, AllowedipsPeerObservation.edge, LookupObservation.edge, LookupObservation.choice,
      Image.Lookup.entry, Image.PeerGet.entry, tested, zero]
    rfl
  · intro q member _
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact nextFrame


#print axioms zero_guard_history
theorem zero_suffix_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : AllowedipsTracePcContract fetch) (traceCmp : AllowedipsTraceConstCmp4Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress) (sp : body.regs.rsp = initial.data.regs.rsp-48)
    (zero : body.regs.get (.low .rbp .W32) = 0)
    (coverage : AllowedipsPeerCoverage.Context) (preempt : BitVec 32)
    (ready : AllowedipsPeerCoverage.CallsReady coverage preempt body)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ address, InRange (initial.data.regs.rsp.toBitVec-48) 56 address →
      ¬(writes address ∨ AllowedipsPeerHistory.scanWrites body coverage address))
    (comparison : AllowedipsPeerCoverage.Context.CompareAllowed coverage preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsPeerObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x3b⟩) :
    Eventually (historyStep fetch) (fun final =>
      Returned initial final.machine returnAddress ∧ final.machine.data.regs.rax = 0 ∧
      AllowedipsPeerCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension history final.history ∧
      ∃ af, ∃ negative wrap dead : MachineState,
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem negative.data.dmem ∧
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem wrap.data.dmem ∧
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem dead.data.dmem ∧
        observeHistory (AllowedipsPeerObservation.edge rxSection) final.history =
        .ok (events ++ [LookupObservation.decision rxSection .refcountAddNzZero true
          ⟨tested (.low .rbp .W32) body af, Image.PeerGet.entry+0xb0⟩ (some (0, 0)),
          LookupObservation.decision rxSection .refcountAddNzNegative false negative,
          LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
          LookupObservation.decision rxSection .peerGetMaybeZeroDead true dead,
          LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, (q.pc ∈ AllowedipsImage.cutPoints ∨ q.pc ∈ Image.cutPoints) →
            EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem q.data.dmem)
      ⟨⟨body, Image.PeerGet.entry+0x3b⟩, history⟩ := by
  have guard := historySteps_eventually fetch 2 _ _
    (zero_guard_history fetch agree body body coverage preempt (ScanFrame.initial body coverage preempt ready)
      zero rxSection history events observed last)
  apply eventually_trans (historyStep fetch) _ _ _ guard
  rintro guarded ⟨af, machine, trace⟩
  have pc : guarded.machine.pc = Image.PeerGet.entry+0xb0 := congrArg MachineState.pc machine
  have data : guarded.machine.data = tested (.low .rbp .W32) body af := congrArg MachineState.data machine
  let event := LookupObservation.decision rxSection .refcountAddNzZero true guarded.machine (some (0, 0))
  have finish := dead_suffix_history fetch agree contract traceCmp initial guarded.machine.data returnAddress
    entry (by simpa only [data, tested] using sp) coverage preempt trace.frame.ready writes
    (by simpa only [data, tested] using frame)
    (by simpa only [data, tested, AllowedipsPeerHistory.scanWrites] using savedSeparate)
    comparison rxSection guarded.history (events ++ [event]) trace.observed (by rw [← pc]; exact trace.last)
  have cursor : (⟨⟨guarded.machine.data, Image.PeerGet.entry+0xb0⟩, guarded.history⟩ : Executed) = guarded := by rw [← pc]
  rw [cursor] at finish
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, endFrame, last, returning, negative, wrap, dead,
    negativeFrame, wrapFrame, deadFrame, seen, tail, recorded, cuts⟩
  simp only [data, tested] at endFrame negativeFrame wrapFrame deadFrame cuts
  obtain ⟨earlier, earlierRecorded, earlierCuts⟩ := trace.extension
  refine ⟨returned, result, state, endFrame, last, trace.stable.returning returning, af, negative, wrap, dead,
    negativeFrame, wrapFrame, deadFrame, ?_, earlier ++ tail, ?_, ?_⟩
  · simpa only [event, machine, List.append_assoc, List.cons_append, List.nil_append] using seen
  · rw [recorded, earlierRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact (earlierCuts q h cut).memory
    · exact cuts q h cut

#print axioms zero_suffix_history

end Binary.AllowedipsPeerGet
