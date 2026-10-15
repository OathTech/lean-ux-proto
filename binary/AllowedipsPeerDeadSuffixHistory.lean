import PeerLiveEntryHistory
import AllowedipsPeerCoverageHistory
import AllowedipsPeerDeadCallbacksHistory
import AllowedipsPeerNullHistory

namespace Binary.AllowedipsPeerGet
open PeerGet LookupHistory
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- The complete zero-count branch from the taken zero guard through the
    actual RET, with all three folded decisions and all appended cuts.
    Reaching this branch is a separate obligation; no peer liveness is assumed. -/
theorem dead_suffix_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : AllowedipsTracePcContract fetch) (traceCmp : AllowedipsTraceConstCmp4Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress) (sp : body.regs.rsp = initial.data.regs.rsp-48)
    (coverage : AllowedipsPeerCoverage.Context) (preempt : BitVec 32)
    (ready : AllowedipsPeerCoverage.CallsReady coverage preempt body)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ address, InRange (initial.data.regs.rsp.toBitVec-48) 56 address →
      ¬(writes address ∨ AllowedipsPeerHistory.scanWrites body coverage address))
    (comparison : AllowedipsPeerCoverage.Context.CompareAllowed coverage preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsPeerObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0xb0⟩) :
    Eventually (historyStep fetch) (fun final =>
      Returned initial final.machine returnAddress ∧ final.machine.data.regs.rax = 0 ∧
      AllowedipsPeerCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension history final.history ∧
      ∃ negative wrap dead : MachineState,
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem negative.data.dmem ∧
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem wrap.data.dmem ∧
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem dead.data.dmem ∧
        observeHistory (AllowedipsPeerObservation.edge rxSection) final.history =
        .ok (events ++ [LookupObservation.decision rxSection .refcountAddNzNegative false negative,
          LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
          LookupObservation.decision rxSection .peerGetMaybeZeroDead true dead,
          LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem q.data.dmem)
      ⟨⟨body, Image.PeerGet.entry+0xb0⟩, history⟩ := by
  have callbacks := dead_callbacks_history fetch agree contract traceCmp body coverage preempt ready
    comparison rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ callbacks
  rintro guarded ⟨negative, wrap, dead, pc₁, negativeFrame, wrapFrame, deadFrame, guardTrace⟩
  let decisions := [LookupObservation.decision rxSection .refcountAddNzNegative false negative,
    LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
    LookupObservation.decision rxSection .peerGetMaybeZeroDead true dead]
  have clear := historySteps_eventually fetch 2 _ _
    (clear_trace fetch agree body guarded.machine.data coverage preempt guardTrace.frame
      rxSection guarded.history (events ++ decisions) guardTrace.observed
      (by rw [← pc₁]; exact guardTrace.last))
  have cursor₁ : (⟨⟨guarded.machine.data, Image.PeerGet.entry+0xdd⟩, guarded.history⟩ : Executed) = guarded := by rw [← pc₁]
  rw [cursor₁] at clear
  apply eventually_trans (historyStep fetch) _ _ _ clear
  rintro cleared ⟨pc₂, bx₂, clearTrace⟩
  have writeEq : AllowedipsPeerHistory.scanWrites cleared.machine.data coverage = AllowedipsPeerHistory.scanWrites body coverage := by
    funext a
    simp only [AllowedipsPeerHistory.scanWrites, clearTrace.frame.stack]
  have finish := finish_9d_history fetch agree contract initial cleared.machine.data returnAddress
    entry (clearTrace.frame.stack.trans sp) coverage preempt clearTrace.frame.ready
    _ (frame.trans clearTrace.frame.memory) (by
      intro address inside
      have h := savedSeparate address inside
      rw [writeEq]
      exact fun written => h (by
        rcases written with (old | earlier) | later
        · exact .inl old
        · exact .inr earlier
        · exact .inr later))
    rxSection cleared.history (events ++ decisions) clearTrace.observed
    (by rw [← pc₂]; exact clearTrace.last)
  have cursor₂ : (⟨⟨cleared.machine.data, Image.PeerGet.entry+0x9d⟩, cleared.history⟩ : Executed) = cleared := by rw [← pc₂]
  rw [cursor₂] at finish
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨returned, _scratch, result, state, endFrame, seen, last, returning, tail, recorded, cuts⟩
  have before := guardTrace.trans clearTrace
  have wholeFrame : EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem final.machine.data.dmem := by
    rw [writeEq] at endFrame
    intro a outside
    exact (clearTrace.frame.memory a outside).trans (endFrame a outside)
  obtain ⟨earlier, earlierRecorded, earlierCuts⟩ := before.extension
  refine ⟨returned, result.trans bx₂, state, wholeFrame, last, before.stable.returning returning, negative, wrap, dead, negativeFrame, wrapFrame, deadFrame, ?_, earlier ++ tail, ?_, ?_⟩
  · simpa only [decisions, List.append_assoc, List.cons_append, List.nil_append] using seen
  · rw [recorded, earlierRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact (earlierCuts q h cut).memory
    · have eq := cuts q h cut
      rw [writeEq] at eq
      intro a outside
      exact (clearTrace.frame.memory a outside).trans (eq a outside)


#print axioms dead_suffix_history
end Binary.AllowedipsPeerGet
