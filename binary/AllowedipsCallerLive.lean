import AllowedipsCallerState

namespace Binary.AllowedipsCaller
open TrustBase AllowedipsPeerGet
local instance : Labels := Image.linkedLabels

/-- Actual helper run after the caller's pushed return word. The raw
history retains the before/after increment split used by correspondence. -/
def LivePost (caller : MachineData) (peer : BitVec 64) (coverage : CommonBitsCoverage.Context)
    (count : UInt32) (rxSection : Nat) (final : Executed) : Prop :=

      Returned (peerCalled caller peer) final.machine AllowedipsPeerExecution.returnAddress ∧
      PeerGet.ScratchMapped (peerCalled caller peer).data final.machine.data.dmem ∧ final.machine.data.regs.rax = (peerCalled caller peer).data.regs.rdi ∧
      CommonBitsCoverage.Context.At coverage final.machine.data.dmem ∧
      final.machine.data.dmem.loadInt ((peerCalled caller peer).data.regs.rdi.toBitVec+0x420) 4 = some ((count.toBitVec+1).toNat : Int) ∧
      EqualOutside (fun a => InRange ((peerCalled caller peer).data.regs.rdi.toBitVec+0x420) 4 a ∨ entryWrites (peerCalled caller peer).data coverage a) (peerCalled caller peer).data.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.IncrementingReturn [(peerCalled caller peer)] final.history ((peerCalled caller peer).data.regs.rdi.toBitVec+0x420) count.toBitVec ∧
      ∃ nullPoint zeroPoint retry negative wrap dead : MachineState,
        EqualOutside (entryWrites (peerCalled caller peer).data coverage) (peerCalled caller peer).data.dmem nullPoint.data.dmem ∧
        EqualOutside (entryWrites (peerCalled caller peer).data coverage) (peerCalled caller peer).data.dmem zeroPoint.data.dmem ∧
        EqualOutside (entryWrites (peerCalled caller peer).data coverage) (AllowedipsPeerGet.incrementEntryMemory (peerCalled caller peer).data count) retry.data.dmem ∧
        EqualOutside (entryWrites (peerCalled caller peer).data coverage) (AllowedipsPeerGet.incrementEntryMemory (peerCalled caller peer).data count) negative.data.dmem ∧
        EqualOutside (entryWrites (peerCalled caller peer).data coverage) (AllowedipsPeerGet.incrementEntryMemory (peerCalled caller peer).data count) wrap.data.dmem ∧
        EqualOutside (entryWrites (peerCalled caller peer).data coverage) (AllowedipsPeerGet.incrementEntryMemory (peerCalled caller peer).data count) dead.data.dmem ∧
        observeHistory (AllowedipsObservation.edge rxSection) final.history =
          .ok ([] ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull false nullPoint,
            LookupObservation.decision rxSection .refcountAddNzZero false zeroPoint (some (count.toNat, 0)),
            LookupObservation.decision rxSection .refcountAddNzRetry false retry,
            LookupObservation.decision rxSection .refcountAddNzNegative false negative,
            LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
            LookupObservation.decision rxSection .peerGetMaybeZeroDead false dead,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ before after, final.history = [(peerCalled caller peer)] ++ before ++ after ∧
          (∀ q ∈ before, (q.pc ∈ AllowedipsImage.cutPoints ∨ q.pc ∈ Image.cutPoints) → EqualOutside (entryWrites (peerCalled caller peer).data coverage) (peerCalled caller peer).data.dmem q.data.dmem) ∧
          (∀ q ∈ after, (q.pc ∈ AllowedipsImage.cutPoints ∨ q.pc ∈ Image.cutPoints) → EqualOutside (entryWrites (peerCalled caller peer).data coverage) (AllowedipsPeerGet.incrementEntryMemory (peerCalled caller peer).data count) q.data.dmem) ∧
          PeerCountPhase.IncrementingReturnAt [(peerCalled caller peer)] ([(peerCalled caller peer)] ++ before) final.history
            ((peerCalled caller peer).data.regs.rdi.toBitVec+0x420) count.toBitVec

theorem live_entry (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : AllowedipsTracePcContract fetch)
    (traceCmp : AllowedipsTraceConstCmp4Contract fetch) (traceByte : AllowedipsTraceConstCmp1Contract fetch)
    (caller : MachineData) (peer : BitVec 64) (coverage : CommonBitsCoverage.Context)
    (ready : Ready coverage caller) (nonnull : peer ≠ 0)
    (count : UInt32) (nonzero : count ≠ 0) (bound : count.toNat+1 < 2^31)
    (field : caller.dmem.loadInt (peer+0x420) 4 = some count.toNat)
    (countStack : ∀ a, InRange (peer+0x420) 4 a → ¬Scratch caller a)
    (countServices : ∀ a, coverage.bytes a → ¬InRange (peer+0x420) 4 a)
    (rxSection : Nat) :
    Eventually (historyStep fetch) (LivePost caller peer coverage count rxSection)
      ⟨(peerCalled caller peer), [(peerCalled caller peer)]⟩ := by
  unfold LivePost
  have entry := ready.entry peer
  have nonnull' : (peerCalled caller peer).data.regs.rdi ≠ 0 := by
    rw [(pushed_shape caller peer).1]
    intro zero
    exact nonnull (congrArg UInt64.toBitVec zero)
  have field' := ready.count peer count field countStack
  apply AllowedipsPeerExecution.live fetch agree contract traceCmp traceByte
    (peerCalled caller peer).data entry.1 nonnull' count nonzero bound field'
    coverage entry.2.1 entry.2.2.1 entry.2.2.2.1 entry.2.2.2.2
    ready.calls.metadataSeparate ready.calls.preemptSeparate
  · intro a bytes inside
    rw [(pushed_shape caller peer).1] at inside
    exact countServices a bytes inside
  · intro a inside written
    rw [(pushed_shape caller peer).1] at inside
    rcases written with stack | buffer
    · rw [scratch_base] at stack
      exact countStack a inside stack
    · exact countServices a (.inr (.inr ⟨buffer.1,.inr buffer.2⟩)) inside

#print axioms live_entry
end Binary.AllowedipsCaller
