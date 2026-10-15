import PeerLiveZeroHistory

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- Accepted nonzero suffix. The history splits at +0x44: earlier cuts
    carry the old count, later cuts the incremented count. The later segment
    also retains non-cut successors +0x48/+0x4a before the physical store. -/
theorem live_suffix_history (fetch : Int64 → Option Decoded)
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
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x3b⟩) :
    Eventually (historyStep fetch) (fun final =>
      Returned initial final.machine returnAddress ∧ final.machine.data.regs.rax = body.regs.rbx ∧
      KcovState coverage preempt final.machine.data.dmem ∧
      final.machine.data.dmem.loadInt body.regs.r13.toBitVec 4 = some ((body.regs.get (.low .rbp .W32)+1).toNat : Int) ∧
      EqualOutside (liveWrites body coverage) body.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      ∃ zeroPoint retry negative wrap dead : MachineState,
        EqualOutside (scanWrites body coverage) body.dmem zeroPoint.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incremented body).dmem retry.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incremented body).dmem negative.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incremented body).dmem wrap.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incremented body).dmem dead.data.dmem ∧
        observeHistory (LookupObservation.edge rxSection) final.history =
          .ok (events ++ [LookupObservation.decision rxSection .refcountAddNzZero false zeroPoint
            (some ((body.regs.get (.low .rbp .W32)).toNat, 0)),
            LookupObservation.decision rxSection .refcountAddNzRetry false retry,
            LookupObservation.decision rxSection .refcountAddNzNegative false negative,
            LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
            LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ before after, final.history = history ++ before ++ after ∧
          (∀ q ∈ before, q.pc ∈ Image.cutPoints →
            EqualOutside (scanWrites body coverage) body.dmem q.data.dmem) ∧
          (∀ q ∈ after, q.pc ∈ Image.cutPoints →
            EqualOutside (scanWrites body coverage) (incremented body).dmem q.data.dmem))
      ⟨⟨body, Image.PeerGet.entry+0x3b⟩, history⟩ := by
  have start := live_zero_call_history fetch agree tracePc body coverage preempt ready nonzero
    rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ start
  rintro atIncrement ⟨af, pc, bx, bp, trace⟩
  have stack := trace.frame.stack
  have address := trace.frame.output
  have old : atIncrement.machine.data.regs.get (.low .rbp .W32) = body.regs.get (.low .rbp .W32) := by
    simp only [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, bp]
  have writesEq : liveWrites atIncrement.machine.data coverage = liveWrites body coverage := by
    funext a; simp only [liveWrites, scanWrites, address, stack]
  have scanEq : scanWrites atIncrement.machine.data coverage = scanWrites body coverage := by
    funext a; simp only [scanWrites, stack]
  have count₂ : atIncrement.machine.data.dmem.loadInt atIncrement.machine.data.regs.r13.toBitVec 4 =
      some (atIncrement.machine.data.regs.get (.low .rbp .W32)).toNat := by
    rw [address, old, ← trace.frame.memory.loadInt body.regs.r13.toBitVec 4 (by
      intro byte bound; exact fieldSeparate _ ⟨byte, bound, rfl⟩)]
    exact count
  let zeroPoint : MachineState := ⟨tested (.low .rbp .W32) body af, Image.PeerGet.entry+0x3f⟩
  let zeroEvent := LookupObservation.decision rxSection .refcountAddNzZero false zeroPoint
    (some ((body.regs.get (.low .rbp .W32)).toNat, 0))
  have finish := increment_finish_history fetch agree tracePc traceCmp traceByte initial atIncrement.machine.data
    returnAddress entry (stack.trans sp) coverage preempt trace.frame.ready count₂
    (by rw [old]; exact nonzero) (by rw [old]; exact bound)
    (by simpa only [address] using countSeparate)
    (by simpa only [address, scanEq] using fieldSeparate)
    _ (frame.trans trace.frame.memory) (by
      intro a inside written
      rw [writesEq] at written
      apply savedSeparate a inside
      rcases written with (h | h) | h
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr h)
    rxSection atIncrement.history (events ++ [zeroEvent]) trace.observed (by rw [← pc]; exact trace.last)
  have cursor : (⟨⟨atIncrement.machine.data, Image.PeerGet.entry+0x44⟩, atIncrement.history⟩ : Executed) = atIncrement := by rw [← pc]
  rw [cursor] at finish
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, finalCount, finalFrame, last, retry, negative, wrap, dead,
    retryFrame, negativeFrame, wrapFrame, deadFrame, seen, tail, recorded, cuts⟩
  have increments : EqualOutside (scanWrites body coverage) (incremented body).dmem
      (incremented atIncrement.machine.data).dmem := by
    simp only [incremented, incrementMemory, address, old]
    exact trace.frame.memory.storeInt _ _ _
  have transfer {m : Mem 64}
      (framed : EqualOutside (scanWrites atIncrement.machine.data coverage) (incremented atIncrement.machine.data).dmem m) :
      EqualOutside (scanWrites body coverage) (incremented body).dmem m := by
    rw [scanEq] at framed
    intro a outside
    exact (increments a outside).trans (framed a outside)
  obtain ⟨earlier, earlierRecorded, earlierCuts⟩ := trace.extension
  refine ⟨returned, result.trans bx, state, ?_, ?_, last, zeroPoint, retry, negative, wrap, dead,
    (fun _ _ => rfl), transfer retryFrame, transfer negativeFrame, transfer wrapFrame, transfer deadFrame,
    ?_, earlier, tail, ?_, ?_, ?_⟩
  · simpa only [address, old] using finalCount
  · rw [writesEq] at finalFrame
    intro a outside
    exact (trace.frame.memory a (fun h => outside (.inr h))).trans (finalFrame a outside)
  · simpa only [zeroEvent, List.append_assoc, List.cons_append, List.nil_append] using seen
  · rw [recorded, earlierRecorded]
  · intro q member cut
    exact (earlierCuts q member cut).memory
  · intro q member cut
    exact transfer (cuts q member cut)

#print axioms live_suffix_history
end Binary.PeerGet
