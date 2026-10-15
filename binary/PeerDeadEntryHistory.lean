import PeerStartHistory
import PeerDeadBodyHistory

namespace Binary.PeerGet
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- Complete actual zero-count path history from entry to the saved return.
    This is physical/observational composition, not all-cut helper adequacy. -/
theorem dead_entry_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : TracePcContract fetch)
    (traceCmp : TraceConstCmp4Contract fetch)
    (s : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame ⟨s, Image.PeerGet.entry⟩ returnAddress) (nonnull : s.regs.rdi ≠ 0)
    (field : s.dmem.loadInt (s.regs.rdi.toBitVec+0x420) 4 = some 0)
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
    (fieldSeparate : ∀ a, InRange (s.regs.rdi.toBitVec+0x420) 4 a → ¬entryWrites s coverage a)
    (comparison : coverage.CompareAllowed preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (LookupObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨s, Image.PeerGet.entry⟩) :
    Eventually (historyStep fetch) (fun final =>
      Returned ⟨s, Image.PeerGet.entry⟩ final.machine returnAddress ∧
      final.machine.data.regs.rax = 0 ∧ LookupCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (entryWrites s coverage) s.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension history final.history ∧
      ∃ nullPoint zeroPoint negative wrap dead : MachineState,
        EqualOutside (entryWrites s coverage) s.dmem nullPoint.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem zeroPoint.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem negative.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem wrap.data.dmem ∧
        EqualOutside (entryWrites s coverage) s.dmem dead.data.dmem ∧
        observeHistory (LookupObservation.edge rxSection) final.history =
          .ok (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull false nullPoint,
            LookupObservation.decision rxSection .refcountAddNzZero true zeroPoint (some (0, 0)),
            LookupObservation.decision rxSection .refcountAddNzNegative false negative,
            LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
            LookupObservation.decision rxSection .peerGetMaybeZeroDead true dead,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (entryWrites s coverage) s.dmem q.data.dmem)
      ⟨⟨s, Image.PeerGet.entry⟩, history⟩ := by
  have headerSeparate : LookupCoverage.Context.Separated coverage (InRange (s.regs.rsp.toBitVec-56) 8) := by
    intro address buffer inside
    obtain ⟨byte, bound, eq⟩ := inside
    exact coverageSeparate address buffer ⟨byte, by omega, eq⟩
  have start := start_history fetch agree contract s coverage preempt state phase entry.1 mapped
    pushSeparate headerSeparate metadataSeparate preemptSeparate rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ start
  rintro body ⟨pc, sp, bx, ready, memory, seen, last, startStable, startTail, startRecorded, startCuts⟩
  have bodyBase : body.machine.data.regs.rsp.toBitVec = s.regs.rsp.toBitVec-48 := by simp [sp]
  have callbackSlot : body.machine.data.regs.rsp.toBitVec-8 = s.regs.rsp.toBitVec-56 := by
    rw [bodyBase, BitVec.sub_sub]
    rfl
  have savedBase : s.regs.rsp.toBitVec-48 = (s.regs.rsp.toBitVec-56)+8 := by
    rw [show (56 : BitVec 64) = 48+8 from rfl, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have savedSeparate : ∀ address, InRange (s.regs.rsp.toBitVec-48) 56 address →
      ¬(LookupCoverage.Context.writes coverage address ∨ scanWrites body.machine.data coverage address) := by
    intro address inside written
    rw [savedBase] at inside
    have outside : ¬LookupCoverage.Context.writes coverage address := fun inBuffer =>
      coverageSeparate address inBuffer (stack_tail_inside _ _ inside)
    rcases written with h | h | h
    · exact outside h
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
  have bodyField : body.machine.data.dmem.loadInt (body.machine.data.regs.rbx.toBitVec+0x420) 4 = some 0 := by
    rw [bx, ← initialFrame.loadInt (s.regs.rdi.toBitVec+0x420) 4 (by
      intro byte bound; exact fieldSeparate _ ⟨byte, bound, rfl⟩)]
    exact field
  have finish := dead_body_history fetch agree contract traceCmp ⟨s, Image.PeerGet.entry⟩
    body.machine.data returnAddress entry sp (by simpa only [bx] using nonnull) bodyField coverage preempt ready
    (by
      intro a inside written
      rw [bx] at inside
      exact fieldSeparate a inside (subset a written))
    (LookupCoverage.Context.writes coverage) memory savedSeparate comparison rxSection body.history events seen
    (by rw [← pc]; exact last)
  have cursor : (⟨⟨body.machine.data, Image.PeerGet.entry+0x12⟩, body.history⟩ : Executed) = body := by rw [← pc]
  rw [cursor] at finish
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, suffixFrame, last, returning, nullPoint, zeroPoint, negative, wrap, dead,
    nullFrame, zeroFrame, negativeFrame, wrapFrame, deadFrame, seen, tail, recorded, cuts⟩
  have transfer {after : Mem 64}
      (frame : EqualOutside (scanWrites body.machine.data coverage) body.machine.data.dmem after) :
      EqualOutside (entryWrites s coverage) s.dmem after := by
    intro address outside
    exact (initialFrame address outside).trans (frame address (fun written => outside (subset address written)))
  refine ⟨returned, result, state, transfer suffixFrame, last, startStable.returning returning,
    nullPoint, zeroPoint, negative, wrap, dead, transfer nullFrame, transfer zeroFrame,
    transfer negativeFrame, transfer wrapFrame, transfer deadFrame, seen, startTail ++ tail, ?_, ?_⟩
  · rw [recorded, startRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact startCuts q h cut
    · exact transfer (cuts q h cut)

#print axioms dead_entry_history
end Binary.PeerGet
