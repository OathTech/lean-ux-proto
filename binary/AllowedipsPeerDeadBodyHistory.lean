import PeerLiveEntryHistory
import AllowedipsPeerCoverageHistory
import AllowedipsPeerNonNullPrefixHistory
import AllowedipsPeerZeroHistory

namespace Binary.AllowedipsPeerGet
open PeerGet LookupHistory
open TrustBase LookupHistory
local instance : Labels := Image.linkedLabels

/-- Complete body of the mapped zero-count path, with all five decisions
    obtained from actual executed edges and the real final RET. -/
theorem dead_body_history (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (contract : AllowedipsTracePcContract fetch)
    (traceCmp : AllowedipsTraceConstCmp4Contract fetch)
    (initial : MachineState) (body : MachineData) (returnAddress : UInt64)
    (entry : EntryFrame initial returnAddress) (sp : body.regs.rsp = initial.data.regs.rsp-48)
    (nonnull : body.regs.rbx ≠ 0)
    (field : body.dmem.loadInt (body.regs.rbx.toBitVec+0x420) 4 = some 0)
    (coverage : AllowedipsPeerCoverage.Context) (preempt : BitVec 32)
    (ready : AllowedipsPeerCoverage.CallsReady coverage preempt body)
    (fieldSeparate : ∀ a, InRange (body.regs.rbx.toBitVec+0x420) 4 a → ¬AllowedipsPeerHistory.scanWrites body coverage a)
    (writes : BitVec 64 → Prop)
    (frame : EqualOutside writes (saveMemory initial.data 7) body.dmem)
    (savedSeparate : ∀ address, InRange (initial.data.regs.rsp.toBitVec-48) 56 address →
      ¬(writes address ∨ AllowedipsPeerHistory.scanWrites body coverage address))
    (comparison : AllowedipsPeerCoverage.Context.CompareAllowed coverage preempt)
    (rxSection : Nat) (history : List MachineState) (events : List LookupObservation.Point)
    (observed : observeHistory (AllowedipsPeerObservation.edge rxSection) history = .ok events)
    (last : history.getLast? = some ⟨body, Image.PeerGet.entry+0x12⟩) :
    Eventually (historyStep fetch) (fun final =>
      Returned initial final.machine returnAddress ∧ final.machine.data.regs.rax = 0 ∧
      AllowedipsPeerCoverage.Context.At coverage preempt final.machine.data.dmem ∧
      EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem final.machine.data.dmem ∧
      final.history.getLast? = some final.machine ∧
      PeerCountPhase.ReturningExtension history final.history ∧
      ∃ nullPoint zeroPoint negative wrap dead : MachineState,
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem nullPoint.data.dmem ∧
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem zeroPoint.data.dmem ∧
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem negative.data.dmem ∧
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem wrap.data.dmem ∧
        EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem dead.data.dmem ∧
        observeHistory (AllowedipsPeerObservation.edge rxSection) final.history =
          .ok (events ++ [LookupObservation.decision rxSection .peerGetMaybeZeroNull false nullPoint,
            LookupObservation.decision rxSection .refcountAddNzZero true zeroPoint (some (0, 0)),
            LookupObservation.decision rxSection .refcountAddNzNegative false negative,
            LookupObservation.decision rxSection .refcountAddNzWraps false wrap,
            LookupObservation.decision rxSection .peerGetMaybeZeroDead true dead,
            LookupObservation.returned "wg_peer_get_maybe_zero" final.machine]) ∧
        ∃ tail, final.history = history ++ tail ∧
          ∀ q ∈ tail, q.pc ∈ Image.cutPoints →
            EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem q.data.dmem)
      ⟨⟨body, Image.PeerGet.entry+0x12⟩, history⟩ := by
  have start :=  nonnull_prefix_history fetch agree contract traceCmp body nonnull 0 field
    coverage preempt ready fieldSeparate comparison rxSection history events observed last
  apply eventually_trans (historyStep fetch) _ _ _ start
  rintro atZero ⟨pc, stack, _, bp, _, ready₂, memory, last₂, prefixStable, af, observed₂, prefixTail, prefixRecorded, prefixCuts⟩
  let nullPoint : MachineState := ⟨tested (.low .rbx .W64) body af, Image.PeerGet.entry+0x1b⟩
  let nullEvent := LookupObservation.decision rxSection .peerGetMaybeZeroNull false nullPoint
  have zero : atZero.machine.data.regs.get (.low .rbp .W32) = 0 := by
    simp [Reg64s.get, Reg64s.get64, Reg.base, Reg.offset, BitVec.drop, BitVec.take, bp]
  have writesEq : AllowedipsPeerHistory.scanWrites atZero.machine.data coverage = AllowedipsPeerHistory.scanWrites body coverage := by
    funext a; simp only [AllowedipsPeerHistory.scanWrites, stack]
  have finish := zero_suffix_history fetch agree contract traceCmp initial atZero.machine.data returnAddress
    entry (stack.trans sp) zero coverage preempt ready₂ _ (frame.trans memory) (by
      intro a inside written
      rw [writesEq] at written
      apply savedSeparate a inside
      rcases written with (h | h) | h
      · exact .inl h
      · exact .inr h
      · exact .inr h)
    comparison rxSection atZero.history (events ++ [nullEvent]) observed₂ (by rw [← pc]; exact last₂)
  have cursor : (⟨⟨atZero.machine.data, Image.PeerGet.entry+0x3b⟩, atZero.history⟩ : Executed) = atZero := by rw [← pc]
  rw [cursor] at finish
  apply eventually_weaken (historyStep fetch) _ _ _ _ finish
  rintro final ⟨returned, result, state, finalFrame, last, returning, af₂, negative, wrap, dead,
    negativeFrame, wrapFrame, deadFrame, seen, tail, recorded, cuts⟩
  have transfer {m : Mem 64}
      (framed : EqualOutside (AllowedipsPeerHistory.scanWrites atZero.machine.data coverage) atZero.machine.data.dmem m) :
      EqualOutside (AllowedipsPeerHistory.scanWrites body coverage) body.dmem m := by
    rw [writesEq] at framed
    intro a outside
    exact (memory a outside).trans (framed a outside)
  refine ⟨returned, result, state, transfer finalFrame, last, prefixStable.returning returning, nullPoint,
    ⟨tested (.low .rbp .W32) atZero.machine.data af₂, Image.PeerGet.entry+0xb0⟩,
    negative, wrap, dead, (fun _ _ => rfl), memory, transfer negativeFrame,
    transfer wrapFrame, transfer deadFrame, ?_, prefixTail ++ tail, ?_, ?_⟩
  · simpa only [nullEvent, List.append_assoc, List.cons_append, List.nil_append] using seen
  · rw [recorded, prefixRecorded, List.append_assoc]
  · intro q member cut
    rcases List.mem_append.mp member with h | h
    · exact prefixCuts q h cut
    · exact transfer (cuts q h cut)

#print axioms dead_body_history
end Binary.AllowedipsPeerGet
