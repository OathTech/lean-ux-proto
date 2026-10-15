import AllowedipsPeerNullEntryHistory
import AllowedipsPeerDeadEntryHistory
import AllowedipsPeerLiveEntryHistory
set_option maxRecDepth 16384
/-! Actual peer-get execution for the allowedips caller.

The public statements expose the fixed coverage context and the global
allowedips observer. Internal modules port the existing physical region
composition to that context, retaining the real histories and count phases.
No index-table relation, owner field or supplied expected history is used.
The caller CALL at lookup+0x114 composes separately with these entry theorems.
-/
namespace Binary.AllowedipsPeerExecution
open TrustBase AllowedipsPeerGet
local instance : Labels := Image.linkedLabels
def returnAddress : UInt64 := (AllowedipsImage.Lookup.entry+0x119).toUInt64

theorem null (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : AllowedipsTracePcContract fetch)
    (s : MachineData)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (null : s.regs.rdi = 0)
    (coverage : CommonBitsCoverage.Context)
    (state : CommonBitsCoverage.Context.At coverage s.dmem)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, AllowedipsPeerCoverage.Context.bytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-56) 56 address)
    (coverageSeparate : AllowedipsPeerCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 64))
    (metadataSeparate : AllowedipsPeerCoverage.Context.Separated coverage (AllowedipsPeerCoverage.Context.metadataBytes coverage))
    (preemptSeparate : AllowedipsPeerCoverage.Context.Separated coverage (InRange preemptCountAddress 4))
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final.machine returnAddress ∧
      final.machine.data.regs.rax = 0 ∧ CommonBitsCoverage.Context.At coverage final.machine.data.dmem ∧
      EqualOutside (entryWrites s coverage) s.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension [⟨s, Image.PeerGet.entry⟩] final.history ∧
      ∃ guard : MachineState, guard.pc = Image.PeerGet.entry+0xdd ∧
        EqualOutside (entryWrites s coverage) s.dmem guard.data.dmem ∧
        observeHistory (AllowedipsObservation.edge rxSection) final.history =
          .ok ([] ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull true guard,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = [⟨s, Image.PeerGet.entry⟩] ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (entryWrites s coverage) s.dmem q.data.dmem)
      ⟨⟨s, Image.PeerGet.entry⟩, [⟨s, Image.PeerGet.entry⟩]⟩ := by
  have run := AllowedipsPeerGet.null_entry_history fetch agree contract s returnAddress entry null coverage coverage.preempt state trivial mapped pushSeparate coverageSeparate metadataSeparate preemptSeparate rxSection [⟨s, Image.PeerGet.entry⟩] [] rfl rfl
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨returned, result, state, frame, last, phase, guard, guardPC, guardFrame, seen, tail, recorded, cuts⟩
  refine ⟨returned, result, state, frame, last, phase, guard, guardPC, guardFrame, ?_, tail, recorded, cuts⟩
  apply AllowedipsPeerObservation.global_history rxSection final.history _ seen
  intro point member tag
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    simp [LookupObservation.decision, LookupObservation.returned] at tag
  exact returned.1

#print axioms null

theorem dead (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : AllowedipsTracePcContract fetch)
    (traceCmp : AllowedipsTraceConstCmp4Contract fetch)
    (s : MachineData)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some 0)
    (coverage : CommonBitsCoverage.Context)
    (state : CommonBitsCoverage.Context.At coverage s.dmem)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, AllowedipsPeerCoverage.Context.bytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-56) 56 address)
    (coverageSeparate : AllowedipsPeerCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 64))
    (metadataSeparate : AllowedipsPeerCoverage.Context.Separated coverage (AllowedipsPeerCoverage.Context.metadataBytes coverage))
    (preemptSeparate : AllowedipsPeerCoverage.Context.Separated coverage (InRange preemptCountAddress 4))
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a → ¬entryWrites s coverage a)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final.machine returnAddress ∧
      final.machine.data.regs.rax = 0 ∧ CommonBitsCoverage.Context.At coverage final.machine.data.dmem ∧
      EqualOutside (entryWrites s coverage) s.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension [⟨s, Image.PeerGet.entry⟩] final.history ∧
      ∃ nullPoint zeroPoint negative wrap dead : MachineState,
        EqualOutside (entryWrites s coverage) s.dmem nullPoint.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem zeroPoint.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem negative.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem wrap.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem dead.data.dmem ∧
        observeHistory (AllowedipsObservation.edge rxSection) final.history =
          .ok ([] ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull false nullPoint,
            LookupObservation.decision rxSection .refcountAddNzZero true zeroPoint (some (0, 0)),
            LookupObservation.decision rxSection .refcountAddNzNegative false negative,
            LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
            LookupObservation.decision rxSection .peerGetMaybeZeroDead true dead,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = [⟨s, Image.PeerGet.entry⟩] ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (entryWrites s coverage) s.dmem q.data.dmem)
      ⟨⟨s, Image.PeerGet.entry⟩, [⟨s, Image.PeerGet.entry⟩]⟩ := by
  have run := AllowedipsPeerGet.dead_entry_history fetch agree contract traceCmp s returnAddress entry nonnull field coverage coverage.preempt state trivial mapped pushSeparate coverageSeparate metadataSeparate preemptSeparate fieldSeparate trivial rxSection [⟨s, Image.PeerGet.entry⟩] [] rfl rfl
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨returned, result, state, frame, last, phase, nullPoint, zeroPoint, negative, wrap, dead,
    nullFrame, zeroFrame, negativeFrame, wrapFrame, deadFrame, seen, tail, recorded, cuts⟩
  refine ⟨returned, result, state, frame, last, phase, nullPoint, zeroPoint, negative, wrap, dead,
    nullFrame, zeroFrame, negativeFrame, wrapFrame, deadFrame, ?_, tail, recorded, cuts⟩
  apply AllowedipsPeerObservation.global_history rxSection final.history _ seen
  intro point member tag
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [LookupObservation.decision, LookupObservation.returned] at tag
  exact returned.1

#print axioms dead

theorem live (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : AllowedipsTracePcContract fetch)
    (traceCmp : AllowedipsTraceConstCmp4Contract fetch) (traceByte : AllowedipsTraceConstCmp1Contract fetch)
    (s : MachineData)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (count : UInt32) (nonzero : count ≠ 0) (bound : count.toNat+1 < 2^31)
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some count.toNat)
    (coverage : CommonBitsCoverage.Context)
    (state : CommonBitsCoverage.Context.At coverage s.dmem)
    (mapped : ∀ n < 7,
      (s.dmem.loadInt (s.regs.rsp.toBitVec - .ofNat 64 ((n+1)*8)) 8).isSome = true)
    (pushSeparate : ∀ address, AllowedipsPeerCoverage.Context.bytes coverage address →
      ¬InRange (s.regs.rsp.toBitVec-56) 56 address)
    (coverageSeparate : AllowedipsPeerCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 64))
    (metadataSeparate : AllowedipsPeerCoverage.Context.Separated coverage (AllowedipsPeerCoverage.Context.metadataBytes coverage))
    (preemptSeparate : AllowedipsPeerCoverage.Context.Separated coverage (InRange preemptCountAddress 4))
    (countSeparate : ∀ a, AllowedipsPeerCoverage.Context.bytes coverage a → ¬InRange (s.regs.rdi.toBitVec+0x420) 4 a)
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a →
      ¬(InRange (s.regs.rsp.toBitVec-56) 64 a ∨ AllowedipsPeerCoverage.Context.writes coverage a))
    (rxSection : Nat) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final.machine returnAddress ∧
      PeerGet.ScratchMapped s final.machine.data.dmem ∧ final.machine.data.regs.rax = s.regs.rdi ∧
      CommonBitsCoverage.Context.At coverage final.machine.data.dmem ∧
      final.machine.data.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some ((count.toBitVec+1).toNat : Int) ∧
      EqualOutside (fun a => InRange (s.regs.rdi.toBitVec+0x420) 4 a ∨ entryWrites s coverage a) s.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.IncrementingReturn [⟨s, Image.PeerGet.entry⟩] final.history (s.regs.rdi.toBitVec+0x420) count.toBitVec ∧
      ∃ nullPoint zeroPoint retry negative wrap dead : MachineState,
        EqualOutside (entryWrites s coverage) s.dmem nullPoint.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem zeroPoint.data.dmem ∧
        EqualOutside (entryWrites s coverage) (AllowedipsPeerGet.incrementEntryMemory s count) retry.data.dmem ∧
        EqualOutside (entryWrites s coverage) (AllowedipsPeerGet.incrementEntryMemory s count) negative.data.dmem ∧
        EqualOutside (entryWrites s coverage) (AllowedipsPeerGet.incrementEntryMemory s count) wrap.data.dmem ∧
        EqualOutside (entryWrites s coverage) (AllowedipsPeerGet.incrementEntryMemory s count) dead.data.dmem ∧
        observeHistory (AllowedipsObservation.edge rxSection) final.history =
          .ok ([] ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull false nullPoint,
            LookupObservation.decision rxSection .refcountAddNzZero false zeroPoint (some (count.toNat, 0)),
            LookupObservation.decision rxSection .refcountAddNzRetry false retry,
            LookupObservation.decision rxSection .refcountAddNzNegative false negative,
            LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
            LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ before after, final.history = [⟨s, Image.PeerGet.entry⟩] ++ before ++ after ∧
          (∀ q ∈ before, q.pc ∈ Image.cutPoints → EqualOutside (entryWrites s coverage) s.dmem q.data.dmem) ∧
          (∀ q ∈ after, q.pc ∈ Image.cutPoints → EqualOutside (entryWrites s coverage) (AllowedipsPeerGet.incrementEntryMemory s count) q.data.dmem) ∧
          PeerCountPhase.IncrementingReturnAt [⟨s, Image.PeerGet.entry⟩] ([⟨s, Image.PeerGet.entry⟩] ++ before) final.history
            (s.regs.rdi.toBitVec+0x420) count.toBitVec)
      ⟨⟨s, Image.PeerGet.entry⟩, [⟨s, Image.PeerGet.entry⟩]⟩ := by
  have run := AllowedipsPeerGet.live_entry_history fetch agree contract traceCmp traceByte s returnAddress entry nonnull count nonzero bound field coverage coverage.preempt state trivial mapped pushSeparate coverageSeparate metadataSeparate preemptSeparate countSeparate fieldSeparate trivial rxSection [⟨s, Image.PeerGet.entry⟩] [] rfl rfl
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  rintro final ⟨returned, scratch, result, state, countRead, frame, last, phase,
    nullPoint, zeroPoint, retry, negative, wrap, dead, nullFrame, zeroFrame, retryFrame, negativeFrame, wrapFrame, deadFrame,
    seen, before, after, recorded, beforeCuts, afterCuts, phaseAt⟩
  refine ⟨returned, scratch, result, state, countRead, frame, last, phase,
    nullPoint, zeroPoint, retry, negative, wrap, dead, nullFrame, zeroFrame, retryFrame, negativeFrame, wrapFrame, deadFrame,
    ?_, before, after, recorded, beforeCuts, afterCuts, phaseAt⟩
  apply AllowedipsPeerObservation.global_history rxSection final.history _ seen
  intro point member tag
  simp only [List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [LookupObservation.decision, LookupObservation.returned] at tag
  exact returned.1

#print axioms live
end Binary.AllowedipsPeerExecution
