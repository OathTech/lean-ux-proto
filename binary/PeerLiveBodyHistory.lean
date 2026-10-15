import PeerNonNullPrefixHistory
import PeerLiveSuffixHistory

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

def peerWrites (body : MachineData) (coverage : LookupCoverage.Context) (a : Address) : Prop :=
  InRange (body.regs.rbx.toBitVec+0x420) 4 a ∨ scanWrites body coverage a

def incrementPeerMemory (body : MachineData) (count : UInt32) : Mem 64 :=
  body.dmem.storeInt (body.regs.rbx.toBitVec+0x420) 4 (count.toBitVec+1).toInt

/-- Complete accepted nonnull body. The recorded history separates the
    pre-increment and post-increment cuts instead of erasing the phase.
    Both segments retain their non-cut instruction successors as well. -/
theorem live_body_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (traceCmp : TraceConstCmp4Contract fetch) (traceByte : TraceConstCmp1Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress) (sp : body.regs.rsp = initial.data.regs.rsp-48)
    (nonnull : body.regs.rbx ≠ 0) (count : UInt32) (nonzero : count ≠ 0) (bound : count.toNat+1 < 2^31)
    (field : body.dmem.loadInt (body.regs.rbx.toBitVec+0x420) 4 = some count.toNat)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32) (ready : LookupCoverage.CallsReady coverage preempt body)
    (countSeparate : ∀ a, LookupCoverage.Context.bytes coverage a → ¬InRange (body.regs.rbx.toBitVec+0x420) 4 a)
    (fieldSeparate : ∀ a, InRange (body.regs.rbx.toBitVec+0x420) 4 a → ¬scanWrites body coverage a)
    (writes : Address → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ a, InRange (initial.data.regs.rsp.toBitVec-48) 56 a → ¬(writes a ∨ peerWrites body coverage a))
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x12⟩) :
    Eventually (historyStep fetch) (fun final =>
      Returned initial final.machine returnAddress ∧
      ScratchMapped initial.data final.machine.data.dmem ∧ final.machine.data.regs.rax = body.regs.rbx ∧
      LookupCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      final.machine.data.dmem.loadInt (body.regs.rbx.toBitVec+0x420) 4 = some ((count.toBitVec+1).toNat : Int) ∧
      EqualOutside (peerWrites body coverage) body.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.IncrementingReturn history final.history (body.regs.rbx.toBitVec+0x420) count.toBitVec ∧
      ∃ nullPoint zeroPoint retry negative wrap dead : MachineState,
        EqualOutside (scanWrites body coverage) body.dmem nullPoint.data.dmem ∧
        EqualOutside (scanWrites body coverage) body.dmem zeroPoint.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incrementPeerMemory body count) retry.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incrementPeerMemory body count) negative.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incrementPeerMemory body count) wrap.data.dmem ∧
        EqualOutside (scanWrites body coverage) (incrementPeerMemory body count) dead.data.dmem ∧
        observeHistory (LookupObservation.edge rxSection) final.history =
          .ok (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull false nullPoint,
            LookupObservation.decision rxSection .refcountAddNzZero false zeroPoint (some (count.toNat, 0)),
            LookupObservation.decision rxSection .refcountAddNzRetry false retry,
            LookupObservation.decision rxSection .refcountAddNzNegative false negative,
            LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
            LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ before after, final.history = history ++ before ++ after ∧
          (∀ q ∈ before, q.pc ∈ Image.cutPoints → EqualOutside (scanWrites body coverage) body.dmem q.data.dmem) ∧
          (∀ q ∈ after, q.pc ∈ Image.cutPoints → EqualOutside (scanWrites body coverage) (incrementPeerMemory body count) q.data.dmem) ∧
          PeerCountPhase.IncrementingReturnAt history (history ++ before) final.history
            (body.regs.rbx.toBitVec+0x420) count.toBitVec)
      ⟨⟨body, Image.PeerGet.entry+0x12⟩, history⟩ := by
  have start := nonnull_prefix_history fetch agree tracePc traceCmp body nonnull count field
    coverage preempt ready fieldSeparate comparison rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ start
  rintro atZero ⟨pc, stack, bx, bp, address, ready₂, memory, last₂, prefixStable, af, observed₂, prefixTail, prefixRecorded, prefixCuts⟩
  have old : atZero.machine.data.regs.get (.low .rbp .W32) = count.toBitVec := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, bp]
    rw [BitVec.extractLsb'_setWidth_of_le (by decide)]
    simp
  have address : atZero.machine.data.regs.r13.toBitVec = body.regs.rbx.toBitVec+0x420 := by simp [address]
  have writesEq : liveWrites atZero.machine.data coverage = peerWrites body coverage := by
    funext a; simp only [liveWrites, peerWrites, scanWrites, address, stack]
  have scanEq : scanWrites atZero.machine.data coverage = scanWrites body coverage := by
    funext a; simp only [scanWrites, stack]
  have field₂ : atZero.machine.data.dmem.loadInt atZero.machine.data.regs.r13.toBitVec 4 =
      some (atZero.machine.data.regs.get (.low .rbp .W32)).toNat := by
    rw [address, old, ← memory.loadInt (body.regs.rbx.toBitVec+0x420) 4 (by
      intro byte bound; exact fieldSeparate _ ⟨byte, bound, rfl⟩)]
    exact field
  have nonzero₂ : atZero.machine.data.regs.get (.low .rbp .W32) ≠ 0 := by
    rw [old]
    intro h
    exact nonzero (UInt32.toBitVec_inj.mp h)
  let nullPoint : MachineState := ⟨tested (.low .rbx .W64) body af, Image.PeerGet.entry+0x1b⟩
  let nullEvent := LookupObservation.decision rxSection .peerGetMaybeZeroNull false nullPoint
  have finish := live_suffix_history fetch agree tracePc traceCmp traceByte initial atZero.machine.data returnAddress
    entry (stack.trans sp) coverage preempt ready₂ field₂ nonzero₂ (by simpa only [old, UInt32.toNat_toBitVec] using bound)
    (by simpa only [address] using countSeparate) (by simpa only [address, scanEq] using fieldSeparate)
    _ (frame.trans memory) (by
      intro a inside written
      rw [writesEq] at written
      apply savedSeparate a inside
      rcases written with (h | h) | h
      · exact .inl h
      · exact .inr (.inr h)
      · exact .inr h)
    comparison rxSection atZero.history (events ++ [nullEvent]) observed₂ (by rw [← pc]; exact last₂)
  have cursor : (⟨⟨atZero.machine.data, Image.PeerGet.entry+0x3b⟩, atZero.history⟩ : Executed) = atZero := by rw [← pc]
  rw [cursor] at finish
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨returned, scratch, result, state, finalCount, finalFrame, last, phase, zeroPoint, retry, negative, wrap, dead,
    zeroFrame, retryFrame, negativeFrame, wrapFrame, deadFrame, seen, before, after, recorded, beforeCuts, afterCuts, phaseAt⟩
  have increments : EqualOutside (scanWrites body coverage) (incrementPeerMemory body count) (incremented atZero.machine.data).dmem := by
    simp only [incrementPeerMemory, incremented, incrementMemory, address, old]
    exact memory.storeInt _ _ _
  have transferOld {m : Mem 64}
      (framed : EqualOutside (scanWrites atZero.machine.data coverage) atZero.machine.data.dmem m) :
      EqualOutside (scanWrites body coverage) body.dmem m := by
    rw [scanEq] at framed
    intro a outside; exact (memory a outside).trans (framed a outside)
  have transferNew {m : Mem 64}
      (framed : EqualOutside (scanWrites atZero.machine.data coverage) (incremented atZero.machine.data).dmem m) :
      EqualOutside (scanWrites body coverage) (incrementPeerMemory body count) m := by
    rw [scanEq] at framed
    intro a outside; exact (increments a outside).trans (framed a outside)
  have phase := prefixStable.incrementing phase
  rw [address, old] at phase
  refine ⟨returned, scratch, result.trans bx, state, ?_, ?_, last, phase, nullPoint, zeroPoint, retry, negative, wrap, dead,
    (fun _ _ => rfl), transferOld zeroFrame, transferNew retryFrame, transferNew negativeFrame,
    transferNew wrapFrame, transferNew deadFrame, ?_, prefixTail ++ before, after, ?_, ?_, ?_, ?_⟩
  · simpa only [address, old] using finalCount
  · rw [writesEq] at finalFrame
    intro a outside; exact (memory a (fun h => outside (.inr h))).trans (finalFrame a outside)
  · simpa only [nullEvent, old, UInt32.toNat_toBitVec, List.append_assoc, List.cons_append, List.nil_append] using seen
  · simp only [recorded, prefixRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact prefixCuts q h cut
    · exact transferOld (beforeCuts q h cut)
  · intro q member cut; exact transferNew (afterCuts q member cut)

  · rw [← List.append_assoc, ← prefixRecorded]
    have h := prefixStable.incrementing_at phaseAt
    simpa only [address, old] using h

#print axioms live_body_history
end Binary.PeerGet
