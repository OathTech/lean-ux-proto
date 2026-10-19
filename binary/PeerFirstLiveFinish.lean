import PeerLiveFinishHistory
import PeerFirstLiveCallbacks
import PeerFirstFinish
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

/-- Accepted live suffix from the successful retry guard through the
    actual RET, retaining the pointer result and all four decisions. -/
theorem live_finish_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (traceCmp : LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (initial : MachineState) (safe : StackSlots outer initial.data.regs.rsp) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress) (sp : body.regs.rsp = initial.data.regs.rsp-48)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (ready : LookupCoverage.CallsReady coverage preempt body)
    (success : body.regs.get (.low .r15 .W8) ≠ 0)
    (oldPositive : (body.regs.get (.low .rbp .W32)).msb = false)
    (newPositive : (body.regs.get (.low .r12 .W32)).msb = false)
    (nonzero : body.regs.get (.low .rbp .W32) ≠ 0)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ address, InRange (initial.data.regs.rsp.toBitVec-48) 56 address →
      ¬(writes address ∨ scanWrites body coverage address))
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x60⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun final =>
      Returned initial final.machine returnAddress ∧
      ScratchMapped initial.data final.machine.data.dmem ∧ final.machine.data.regs.rax = body.regs.rbx ∧
      LookupCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (scanWrites body coverage) body.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension history final.history ∧
      ∃ retry negative wrap dead : MachineState,
        EqualOutside (scanWrites body coverage) body.dmem retry.data.dmem ∧
        EqualOutside (scanWrites body coverage) body.dmem negative.data.dmem ∧
        EqualOutside (scanWrites body coverage) body.dmem wrap.data.dmem ∧
        EqualOutside (scanWrites body coverage) body.dmem dead.data.dmem ∧
        observeHistory (LookupObservation.edge rxSection) final.history =
        .ok (events ++ [LookupObservation.decision rxSection .refcountAddNzRetry false retry,
          LookupObservation.decision rxSection .refcountAddNzNegative false negative,
          LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
          LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead,
          LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (scanWrites body coverage) body.dmem q.data.dmem)
      ⟨⟨body, Image.PeerGet.entry+0x60⟩, history⟩ := by
  have callbacks := live_callbacks_history fetch agree contract traceCmp body (safe.call sp) coverage preempt ready
    success oldPositive newPositive nonzero comparison rxSection history events observed last
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ callbacks
  rintro cleared ⟨retry, negative, wrap, dead, pc₂, bx₂, _, retryFrame, negativeFrame, wrapFrame, deadFrame, clearTrace⟩
  let decisions := [LookupObservation.decision rxSection .refcountAddNzRetry false retry,
    LookupObservation.decision rxSection .refcountAddNzNegative false negative,
    LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
    LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead]
  have writeEq : scanWrites cleared.machine.data coverage = scanWrites body coverage := by
    funext a
    simp only [scanWrites, clearTrace.frame.stack]
  have finish := finish_9d_history fetch agree contract initial safe cleared.machine.data returnAddress
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
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ finish
  rintro final ⟨returned, scratch, result, state, endFrame, seen, last, returning, tail, recorded, cuts⟩
  have wholeFrame : EqualOutside (scanWrites body coverage) body.dmem final.machine.data.dmem := by
    rw [writeEq] at endFrame
    intro a outside
    exact (clearTrace.frame.memory a outside).trans (endFrame a outside)
  obtain ⟨earlier, earlierRecorded, earlierCuts⟩ := clearTrace.extension
  refine ⟨returned, scratch, result.trans bx₂, state, wholeFrame, last, clearTrace.stable.returning returning, retry, negative, wrap, dead, retryFrame, negativeFrame, wrapFrame, deadFrame, ?_, earlier ++ tail, ?_, ?_⟩
  · simpa only [decisions, List.append_assoc, List.cons_append, List.nil_append] using seen
  · rw [recorded, earlierRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact (earlierCuts q h cut).memory
    · have eq := cuts q h cut
      rw [writeEq] at eq
      intro a outside
      exact (clearTrace.frame.memory a outside).trans (eq a outside)


#print axioms live_finish_history
end Binary.PeerGet.First
