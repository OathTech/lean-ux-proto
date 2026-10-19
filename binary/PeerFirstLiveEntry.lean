import PeerLiveEntryHistory
import PeerFirstStart
import PeerFirstLiveBody
namespace Binary.PeerGet.First
open TrustBase LookupHistory Callback LookupHistory.First
local instance : Labels := Image.linkedLabels
variable {outer : UInt64}

/-- Complete accepted live helper history from entry through RET, with
    actual decisions and separate physical frames before/after the increment.
    This is not yet the helper all-cut R theorem. -/
theorem live_entry_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (traceCmp : LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4)) (traceByte : LeafService fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1))
    (s : MachineData) (safe : StackSlots outer s.regs.rsp) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (count : UInt32) (nonzero : count ≠ 0) (bound : count.toNat+1 < 2^31)
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some count.toNat)
    (coverage : LookupCoverage.Context) (preempt : BitVec 32)
    (state : LookupCoverage.Context.At coverage preempt s.dmem)
    (phase : preempt = coverage.entryPreempt ∨ preempt = 512+coverage.entryPreempt)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, LookupCoverage.Context.bytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-56) 56 address)
    (coverageSeparate : LookupCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 64))
    (metadataSeparate : LookupCoverage.Context.Separated coverage (LookupCoverage.Context.metadataBytes coverage))
    (preemptSeparate : LookupCoverage.Context.Separated coverage (InRange preemptCountAddress 4))
    (countSeparate : ∀ a, LookupCoverage.Context.bytes coverage a → ¬InRange (s.regs.rdi.toBitVec+0x420) 4 a)
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a →
      ¬(InRange (s.regs.rsp.toBitVec-56) 64 a ∨ LookupCoverage.Context.writes coverage a))
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.PeerGet.entry⟩) :
    Eventually (guardedHistoryStep fetch (StackGuard outer)) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final.machine returnAddress ∧
      PeerGet.ScratchMapped s final.machine.data.dmem ∧ final.machine.data.regs.rax = s.regs.rdi ∧
      LookupCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      final.machine.data.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some ((count.toBitVec+1).toNat : Int) ∧
      EqualOutside (fun a => InRange (s.regs.rdi.toBitVec+0x420) 4 a ∨ entryWrites s coverage a) s.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.IncrementingReturn history final.history (s.regs.rdi.toBitVec+0x420) count.toBitVec ∧
      ∃ nullPoint zeroPoint retry negative wrap dead : MachineState,
        EqualOutside (entryWrites s coverage) s.dmem nullPoint.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem zeroPoint.data.dmem ∧
        EqualOutside (entryWrites s coverage) (incrementEntryMemory s count) retry.data.dmem ∧
        EqualOutside (entryWrites s coverage) (incrementEntryMemory s count) negative.data.dmem ∧
        EqualOutside (entryWrites s coverage) (incrementEntryMemory s count) wrap.data.dmem ∧
        EqualOutside (entryWrites s coverage) (incrementEntryMemory s count) dead.data.dmem ∧
        observeHistory (LookupObservation.edge rxSection) final.history =
          .ok (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull false nullPoint,
            LookupObservation.decision rxSection .refcountAddNzZero false zeroPoint (some (count.toNat, 0)),
            LookupObservation.decision rxSection .refcountAddNzRetry false retry,
            LookupObservation.decision rxSection .refcountAddNzNegative false negative,
            LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
            LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ before after, final.history = history ++ before ++ after ∧
          (∀ q ∈ before, q.pc ∈ Image.cutPoints → EqualOutside (entryWrites s coverage) s.dmem q.data.dmem) ∧
          (∀ q ∈ after, q.pc ∈ Image.cutPoints → EqualOutside (entryWrites s coverage) (incrementEntryMemory s count) q.data.dmem) ∧
          PeerCountPhase.IncrementingReturnAt history (history ++ before) final.history
            (s.regs.rdi.toBitVec+0x420) count.toBitVec)
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  have headerSeparate : LookupCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 8) := by
    intro address buffer inside
    obtain ⟨byte, bound, eq⟩ := inside
    exact coverageSeparate address buffer ⟨byte, by omega, eq⟩
  have start := start_history fetch agree contract s safe coverage preempt state phase entry.1 mapped
    pushSeparate headerSeparate metadataSeparate preemptSeparate rxSection history events observed last
  apply eventually_trans (guardedHistoryStep fetch (StackGuard outer)) _ _ _ start
  rintro body ⟨pc, sp, bx, ready, memory, seen, last, startStable, startTail, startRecorded, startCuts⟩
  have bodyBase : body.machine.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec-48 := by simp [sp]
  have callbackSlot : body.machine.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-56 := by
    rw [bodyBase, BitVec.sub_sub]
    rfl
  have savedBase : s.regs.rsp.toBitVec-48 = (s.regs.rsp.toBitVec-56)+8 := by
    rw [show (56 : BitVec 64) = 48+8 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have savedSeparate : ∀ address, InRange (s.regs.rsp.toBitVec-48) 56 address →
      ¬(LookupCoverage.Context.writes coverage address ∨ peerWrites body.machine.data coverage address) := by
    intro address inside written
    rw [savedBase] at inside
    have outside : ¬LookupCoverage.Context.writes coverage address := fun inBuffer =>
      coverageSeparate address inBuffer (stack_tail_inside _ _ inside)
    rcases written with h | h | h | h
    · exact outside h
    · rw [bx] at h
      exact fieldSeparate address h (.inl (stack_tail_inside _ _ inside))
    · rw [callbackSlot] at h
      exact stack_tail_disjoint_header _ _ inside h
    · exact outside h
  have initialFrame : EqualOutside (entryWrites s coverage) s.dmem body.machine.data.dmem :=
    (saveMemory_frame s 7 (by decide)).trans memory
  have subset : ∀ address, scanWrites body.machine.data coverage address → entryWrites s coverage address := by
    intro address written
    rcases written with stack | buffer
    · rw [callbackSlot] at stack
      obtain ⟨byte, bound, eq⟩ := stack
      exact .inl ⟨byte, by omega, eq⟩
    · exact .inr buffer
  have fieldOutside : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a → ¬entryWrites s coverage a := by
    intro a inside written
    apply fieldSeparate a inside
    rcases written with stack | buffer
    · obtain ⟨byte, bound, eq⟩ := stack
      exact .inl ⟨byte, by omega, eq⟩
    · exact .inr buffer
  have bodyField : body.machine.data.dmem.loadInt (body.machine.data.regs.rbx.toBitVec+0x420) 4 = some count.toNat := by
    rw [bx, ← initialFrame.loadInt (s.regs.rdi.toBitVec+0x420) 4 (by
      intro byte bound; exact fieldOutside _ ⟨byte, bound, rfl⟩)]
    exact field
  have finish := live_body_history fetch agree contract traceCmp traceByte ⟨s, Image.PeerGet.entry⟩ safe
    body.machine.data returnAddress entry sp (by simpa only [bx] using nonnull) count nonzero bound bodyField
    coverage preempt ready (by simpa only [bx] using countSeparate)
    (by
      intro a inside written
      rw [bx] at inside
      exact fieldOutside a inside (subset a written))
    (LookupCoverage.Context.writes coverage) memory savedSeparate comparison rxSection body.history events seen
    (by rw [← pc]; exact last)
  have cursor : (⟨⟨body.machine.data, Image.PeerGet.entry+0x12⟩, body.history⟩ : Executed) = body := by rw [← pc]
  rw [cursor] at finish
  apply eventually_weaken (guardedHistoryStep fetch (StackGuard outer)) _ _ _ _ finish
  rintro final ⟨returned, scratch, result, state, finalCount, finalFrame, last, phase, nullPoint, zeroPoint, retry, negative, wrap, dead,
    nullFrame, zeroFrame, retryFrame, negativeFrame, wrapFrame, deadFrame, seen, before, after, recorded, beforeCuts, afterCuts, phaseAt⟩
  have transferOld {m : Mem 64}
      (framed : EqualOutside (scanWrites body.machine.data coverage) body.machine.data.dmem m) :
      EqualOutside (entryWrites s coverage) s.dmem m := by
    intro a outside
    exact (initialFrame a outside).trans (framed a (fun h => outside (subset a h)))
  have increments : EqualOutside (entryWrites s coverage) (incrementEntryMemory s count)
      (incrementPeerMemory body.machine.data count) := by
    simp only [incrementEntryMemory, incrementPeerMemory, bx]
    exact initialFrame.storeInt _ _ _
  have transferNew {m : Mem 64}
      (framed : EqualOutside (scanWrites body.machine.data coverage) (incrementPeerMemory body.machine.data count) m) :
      EqualOutside (entryWrites s coverage) (incrementEntryMemory s count) m := by
    intro a outside
    exact (increments a outside).trans (framed a (fun h => outside (subset a h)))
  have phase := startStable.incrementing phase
  rw [bx] at phase
  refine ⟨returned, scratch, result.trans bx, state, ?_, ?_, last, phase, nullPoint, zeroPoint, retry, negative, wrap, dead,
    transferOld nullFrame, transferOld zeroFrame, transferNew retryFrame, transferNew negativeFrame,
    transferNew wrapFrame, transferNew deadFrame, seen, startTail ++ before, after, ?_, ?_, ?_, ?_⟩
  · simpa only [bx] using finalCount
  · intro a outside
    exact (initialFrame a (fun h => outside (.inr h))).trans (finalFrame a (by
      rintro (countByte | scratch)
      · rw [bx] at countByte
        exact outside (.inl countByte)
      · exact outside (.inr (subset a scratch))))
  · simp only [recorded, startRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact startCuts q h cut
    · exact transferOld (beforeCuts q h cut)
  · intro q member cut; exact transferNew (afterCuts q member cut)

  · rw [← List.append_assoc, ← startRecorded]
    have h := startStable.incrementing_at phaseAt
    simpa only [bx] using h

#print axioms live_entry_history
end Binary.PeerGet.First
