import PeerIncrementCallHistory
import PeerLiveFinishHistory

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

def liveWrites (body : MachineData) (coverage : KcovLayout) (a : Address) : Prop :=
  InRange body.regs.r13.toBitVec 4 a ∨ scanWrites body coverage a

/-- Successful physical increment through RET. The count/callback separation
    derives preservation of the increment; it is not a fresh endpoint premise. -/
theorem increment_finish_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch)
    (tracePc : TracePcContract fetch) (traceCmp : TraceConstCmp4Contract fetch)
    (traceByte : TraceConstCmp1Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress) (sp : body.regs.rsp = initial.data.regs.rsp-48)
    (coverage : KcovLayout) (preempt : BitVec 32) (ready : CallsReady coverage preempt body)
    (count : body.dmem.loadInt body.regs.r13.toBitVec 4 = some (body.regs.get (.low .rbp .W32)).toNat)
    (nonzero : body.regs.get (.low .rbp .W32) ≠ 0)
    (bound : (body.regs.get (.low .rbp .W32)).toNat+1 < 2^31)
    (countSeparate : ∀ a, KcovStateBytes coverage a → ¬InRange body.regs.r13.toBitVec 4 a)
    (fieldSeparate : ∀ a, InRange body.regs.r13.toBitVec 4 a → ¬scanWrites body coverage a)
    (writes : Address → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ a, InRange (initial.data.regs.rsp.toBitVec-48) 56 a →
      ¬(writes a ∨ liveWrites body coverage a))
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x44⟩) :
    Eventually (historyStep fetch) (fun final =>
      Returned initial final.machine returnAddress ∧ final.machine.data.regs.rax = body.regs.rbx ∧
      KcovState coverage preempt final.machine.data.dmem ∧
      final.machine.data.dmem.loadInt body.regs.r13.toBitVec 4 = some ((body.regs.get (.low .rbp .W32)+1).toNat : Int) ∧
      EqualOutside (liveWrites body coverage) body.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      ∃ retry negative wrap dead : MachineState,
        EqualOutside (scanWrites body coverage) (incremented body).dmem retry.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incremented body).dmem negative.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incremented body).dmem wrap.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incremented body).dmem dead.data.dmem ∧
        observeHistory (LookupObservation.edge rxSection) final.history =
          .ok (events ++ [LookupObservation.decision rxSection .refcountAddNzRetry false retry,
            LookupObservation.decision rxSection .refcountAddNzNegative false negative,
            LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
            LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (scanWrites body coverage) (incremented body).dmem q.data.dmem)
      ⟨⟨body, Image.PeerGet.entry+0x44⟩, history⟩ := by
  have call := increment_call_history fetch agree traceByte body coverage preempt ready count countSeparate
    rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ call
  rintro testedState ⟨af, pc, bx, bp, trace⟩
  have regs := incremented_registers body
  have stack : testedState.machine.data.regs.rsp = body.regs.rsp := by
    simpa only [incFinal_shape, regs.1] using trace.frame.stack
  have writesEq : scanWrites testedState.machine.data coverage = scanWrites body coverage := by
    funext a; simp only [scanWrites, stack]
  have incWritesEq : scanWrites (incFinal body af) coverage = scanWrites body coverage := by
    funext a; simp only [scanWrites, incFinal_shape, regs.1]
  have memory : EqualOutside (scanWrites body coverage) (incremented body).dmem testedState.machine.data.dmem := by
    have h := trace.frame.memory
    rw [incWritesEq] at h
    simpa only [incFinal_shape] using h
  have testBP : testedState.machine.data.regs.get (.low .rbp .W32) = body.regs.get (.low .rbp .W32) := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, bp]
  have testR12 : testedState.machine.data.regs.get (.low .r12 .W32) = body.regs.get (.low .rbp .W32)+1 := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, trace.frame.query, incFinal_shape] using regs.2.2.2.2.1
  have testR15 : testedState.machine.data.regs.get (.low .r15 .W8) = 1 := by
    simpa only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, trace.frame.saved, incFinal_shape] using regs.2.2.2.2.2
  have signs := count_signs (body.regs.get (.low .rbp .W32)).toNat bound
  simp only [BitVec.ofNat_toNat] at signs
  have finish := live_finish_history fetch agree tracePc traceCmp initial testedState.machine.data returnAddress
    entry (stack.trans sp) coverage preempt trace.frame.ready
    (by rw [testR15]; decide) (by rw [testBP]; exact signs.1) (by rw [testR12]; exact signs.2)
    (by rw [testBP]; exact nonzero) _ ((frame.trans (incremented_frame body)).trans memory) (by
      intro a inside written
      rw [writesEq] at written
      apply savedSeparate a inside
      rcases written with ((h | h) | h) | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
      · exact .inr (.inr h))
    rxSection testedState.history events trace.observed (by rw [← pc]; exact trace.last)
  have cursor : (⟨⟨testedState.machine.data, Image.PeerGet.entry+0x60⟩, testedState.history⟩ : Executed) = testedState := by rw [← pc]
  rw [cursor] at finish
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, finalFrame, last, retry, negative, wrap, dead,
    retryFrame, negativeFrame, wrapFrame, deadFrame, seen, tail, recorded, cuts⟩
  have afterIncrement {m : Mem 64}
      (framed : EqualOutside (scanWrites testedState.machine.data coverage) testedState.machine.data.dmem m) :
      EqualOutside (scanWrites body coverage) (incremented body).dmem m := by
    rw [writesEq] at framed
    intro a outside
    exact (memory a outside).trans (framed a outside)
  have transfer {m : Mem 64}
      (framed : EqualOutside (scanWrites testedState.machine.data coverage) testedState.machine.data.dmem m) :
      EqualOutside (liveWrites body coverage) body.dmem m :=
    (incremented_frame body).trans (afterIncrement framed)
  obtain ⟨earlier, earlierRecorded, earlierCuts⟩ := trace.extension
  refine ⟨returned, result.trans bx, state, ?_, transfer finalFrame, last,
    retry, negative, wrap, dead, afterIncrement retryFrame, afterIncrement negativeFrame, afterIncrement wrapFrame, afterIncrement deadFrame,
    seen, earlier ++ tail, ?_, ?_⟩
  · rw [← (afterIncrement finalFrame).loadInt body.regs.r13.toBitVec 4 (by
      intro byte bound; exact fieldSeparate _ ⟨byte, bound, rfl⟩)]
    exact incremented_count body
  · rw [recorded, earlierRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · have framed := (earlierCuts q h cut).memory
      rw [incWritesEq] at framed
      have framed : EqualOutside (scanWrites body coverage) (incremented body).dmem q.data.dmem := by
        simpa only [incFinal_shape] using framed
      exact framed
    · exact afterIncrement (cuts q h cut)

#print axioms increment_finish_history
end Binary.PeerGet
