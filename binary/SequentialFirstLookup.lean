import SequentialLookup
import SequentialFirstResult
import SequentialFirstTails
import LookupFirstFromPre
import LookupFirstHelperFromBucket
namespace Binary.Sequential.First
open Leanux Leanux.WG TrustBase LookupRelation LookupHistory LookupObservation Callback
local instance : Labels := Image.linkedLabels
theorem selected_execution (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (traceCmp : LeafService fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4)) (traceConstCmp : LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (traceByte : LeafService fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1)) (bh : LeafService fetch (.ofNat 0xffffffff810732c0) BhEnableReady (fun _ => InRange preemptCountAddress 4) (fun before after => ∀ old : BitVec 32, before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) → after.data.dmem.loadInt preemptCountAddress 4 = some ((old-before.data.regs.get (.low .rsi .W32)).toNat : Int)))
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World)
    (pre : Pre_lookup c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (answer : Option (IndexOwner × PeerId)) (finalWorld : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, finalWorld)) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp))
      (fun final => Post c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world answer finalWorld final.machine)
      ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  obtain ⟨v, entry⟩ := pre
  obtain ⟨helperAnswer, helperFinal, middle, sourcePoints, helperAccepted, calledRun, continuation, fullSource⟩ :=
    lookup_accepts_helper c coverage preempt returnAddress _ world v entry owner focused answer finalWorld accepted
  obtain ⟨setWorld, setRun, answerEq, finalEq, sourceEq⟩ :=
    afterHelper_accepted owner helperAnswer middle sourcePoints helperFinal finalWorld answer continuation
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _
    (LookupRelation.First.start_from_entry fetch agree tracePc c coverage preempt returnAddress s world v entry)
  intro started startedAt
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _
    (LookupRelation.First.header_from_started fetch agree c coverage preempt returnAddress s world v entry started startedAt)
  intro head headAt
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _
    (LookupRelation.First.bucket_from_head fetch agree tracePc traceCmp traceConstCmp c coverage preempt returnAddress s world v entry head headAt)
  intro bucket bucketAt
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _
    (LookupRelation.First.helper_call_from_bucket fetch agree tracePc c coverage preempt returnAddress s world v entry bucket bucketAt owner focused)
  intro helper before
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _
    (helper_from_call fetch agree tracePc traceConstCmp traceByte c coverage preempt returnAddress s world v entry bucket helper
      bucketAt owner focused before helperAnswer helperFinal helperAccepted)
  intro current after
  have run := result_from_helper fetch agree c coverage preempt returnAddress s world v entry bucket helper current owner focused
      before helperAnswer helperFinal setWorld after setRun
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ run
  intro result resultAt
  obtain ⟨saved, frame, ready, output, ownerReg, peerReg, pc⟩ :=
    selected_result_ready c coverage preempt returnAddress s world v entry bucket helper current result
      owner focused bucketAt before helperAnswer helperFinal setWorld after resultAt
  obtain ⟨_, view, needed, _, _, mapped, _, related⟩ := resultAt
  have sourceView : ∃ view, project c finalWorld = some view ∧ view.bucket = v.bucket := by
    simpa only [finalEq] using view
  have endpoint : Related c result.machine finalWorld := by simpa only [finalEq] using related
  cases helperAnswer with
  | none =>
    have finish := clear_finish fetch agree tracePc bh c coverage preempt returnAddress s world v entry result
      (by simpa only [Option.isSome_none, Bool.false_eq_true, ite_false] using pc)
      finalWorld sourceView saved ready frame endpoint
    apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ finish
    rintro final ⟨ret, zero, frame, related, coverageAt, countAt⟩
    exact ⟨ret, by simpa only [answerEq, Option.map_none, LookupResult] using zero,
      related, v, entry, frame, coverageAt, countAt,
      pending_from_frame c coverage preempt returnAddress s final.machine.data world v entry frame⟩
  | some pid =>
    have finish := live_finish fetch agree tracePc bh c coverage preempt returnAddress s world v entry result
      (by simpa only [Option.isSome_some, ite_true] using pc)
      finalWorld sourceView saved ready frame output (needed rfl) (mapped rfl) endpoint
    apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ finish
    rintro final ⟨ret, value, outValue, frame, related, coverageAt, countAt⟩
    refine ⟨ret, ?_, related, v, entry, frame, coverageAt, countAt,
      pending_from_frame c coverage preempt returnAddress s final.machine.data world v entry frame⟩
    simp only [answerEq, Option.map_some, LookupResult]
    constructor
    · rw [value]; exact ownerReg
    · rw [outValue]
      have h := congrArg BitVec.toNat peerReg
      simpa only [OwnerWord.pointer, UInt64.toNat_toBitVec] using congrArg (fun n : Nat => some (n : Int)) h

theorem miss_execution (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc))
    (traceCmp : LeafService fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4)) (traceConstCmp : LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4))
    (bh : LeafService fetch (.ofNat 0xffffffff810732c0) BhEnableReady (fun _ => InRange preemptCountAddress 4) (fun before after => ∀ old : BitVec 32, before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) → after.data.dmem.loadInt preemptCountAddress 4 = some ((old-before.data.regs.get (.low .rsi .W32)).toNat : Int)))
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (s : MachineData) (world : World)
    (pre : Pre_lookup c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world)
    (focused : c.focus.owner = none)
    (answer : Option (IndexOwner × PeerId)) (finalWorld : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, finalWorld)) :
    Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp))
      (fun final => Post c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world answer finalWorld final.machine)
      ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  obtain ⟨v, entry⟩ := pre
  obtain ⟨answerEq, finalEq⟩ := lookup_no_owner_accepted c coverage preempt ra _ world v entry focused answer finalWorld accepted
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _
    (LookupRelation.First.start_from_entry fetch agree tracePc c coverage preempt ra s world v entry)
  intro started startedAt
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _
    (LookupRelation.First.header_from_started fetch agree c coverage preempt ra s world v entry started startedAt)
  intro head headAt
  apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _
    (LookupRelation.First.bucket_from_head fetch agree tracePc traceCmp traceConstCmp c coverage preempt ra s world v entry head headAt)
  intro bucket bucketAt
  have saved := outer_saved_bucket c coverage preempt ra s world v entry bucket bucketAt
  have frame := bucket_write_frame c coverage preempt ra s world v entry bucket bucketAt
  obtain ⟨head, headAt, _, stop, bucketFrame, delta, observed, raw, matched, aligned, related, _, tags, _⟩ := bucketAt
  have places := selected_stop_none c v bucket.machine (entry.focus.1.trans focused) stop
  let seen := [entryPoint s] ++ delta
  have projected : project c finalWorld = some v := by
    rw [finalEq, LookupSearch.result_world]
    exact entry.projected
  have sourceView : ∃ view, project c finalWorld = some view ∧ view.bucket = v.bucket := ⟨v, projected, rfl⟩
  have inactive : helperActive seen = false := by
    rw [helperActive_append_decisions _ _ tags]
    rfl
  have noReturn : lastHelperReturn seen = none := lastHelperReturn_append_decisions _ _ tags rfl
  have related' : R c bucket.history seen bucket.machine finalWorld := by simpa only [finalEq] using related
  have endpoint : Related c bucket.machine finalWorld := by
    obtain ⟨view, projected, physical⟩ := related'.2.1
    exact ⟨view, projected, of_physical physical (countPhase_inactive _ _ inactive)
      (ownerPending_none _ _ noReturn)⟩
  have close (current : Executed) (pc : current.machine.pc = Image.Lookup.entry+0x71)
      (saved : OuterSaved s current.machine.data)
      (ready : LookupCoverage.CallsReady ⟨coverage, preempt, v⟩ (512+preempt) current.machine.data)
      (frame : EqualOutside (LookupWrites c coverage preempt s v) s.dmem current.machine.data.dmem)
      (related : Related c current.machine finalWorld) :
      Eventually (guardedHistoryStep fetch (StackGuard s.regs.rsp))
        (fun final => Post c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world answer finalWorld final.machine) current := by
    have run := clear_finish fetch agree tracePc bh c coverage preempt ra s world v entry current pc finalWorld sourceView
      saved ready frame related
    apply eventually_weaken (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ _ run
    rintro final ⟨ret, zero, frame, related, coverageAt, countAt⟩
    exact ⟨ret, by simpa only [answerEq, LookupResult] using zero, related, v, entry, frame, coverageAt, countAt,
      pending_from_frame c coverage preempt ra s final.machine.data world v entry frame⟩
  rcases places with pc | pc
  · have scratch : ∀ view, project c finalWorld = some view → ∀ a, Reads c view a →
        ¬scanWrites bucket.machine.data ⟨coverage, preempt, v⟩ a := by
      intro view projection a read written
      have eq : view = v := Option.some.inj (projection.symm.trans projected)
      subst view
      apply entry.readsScratch a read
      rcases written with stack | covered
      · exact .inl (callback_stack_in c s bucket.machine.data saved.stack a stack)
      · exact .inr (.inl covered)
    have run := callback (outer := s.regs.rsp) fetch agree tracePc bucket 0x6c (.inl rfl) pc
      ⟨coverage, preempt, v⟩ (512+preempt) (by rw [saved.stack]; constructor <;> stack_not_return) bucketFrame.ready
    apply eventually_trans (guardedHistoryStep fetch (StackGuard s.regs.rsp)) _ _ _ run
    rintro callback ⟨cbPC, _, _, traced⟩
    have cbSaved := saved.frame traced.stack traced.saved _ traced.memory (by
      intro a inside written
      rcases written with stack | covered
      · apply outer_callback_apart s a inside
        simpa only [saved.stack, UInt64.toBitVec_sub, BitVec.sub_sub,
          show (40 : UInt64).toBitVec+8 = (48 : BitVec 64) from rfl] using stack
      · exact entry.coverageStack a covered (outer_live c s a inside))
    exact close callback (by simpa only [pc, show Image.Lookup.entry+0x6c+5 = Image.Lookup.entry+0x71 from rfl] using cbPC)
      cbSaved traced.ready (lookup_frame_callback c coverage preempt s bucket.machine.data callback.machine.data v saved.stack frame traced.memory)
      (endpoint.frame traced.memory scratch)
  · exact close bucket pc saved bucketFrame.ready frame endpoint

/-- Sibling endpoint simulation under sequential Kraken execution. The
entry predicate is exactly M1's, including dead peers and output aliases.
This deliberately omits internal correspondence and the M1 permission audit;
it makes no claim of concurrent contextual refinement. -/
theorem lookup_simulation (fetch : Int64 → Option Decoded)
    (decoder : AnchoredDecoderAgreement fetch)
    (tracePc : LeafService fetch (.ofNat 0xffffffff810f3100) (KcovReady .pc) (KcovWrites .pc) (KcovEffect .pc)) (traceCmp4 : LeafService fetch (.ofNat 0xffffffff810f3e80) (KcovReady .cmp4) (KcovWrites .cmp4) (KcovEffect .cmp4))
    (traceConstCmp4 : LeafService fetch (.ofNat 0xffffffff810f3f00) (KcovReady .constCmp4) (KcovWrites .constCmp4) (KcovEffect .constCmp4)) (traceConstCmp1 : LeafService fetch (.ofNat 0xffffffff810f3ec0) (KcovReady .constCmp1) (KcovWrites .constCmp1) (KcovEffect .constCmp1))
    (bhEnable : LeafService fetch (.ofNat 0xffffffff810732c0) BhEnableReady (fun _ => InRange preemptCountAddress 4) (fun before after => ∀ old : BitVec 32, before.data.dmem.loadInt preemptCountAddress 4 = some (old.toNat : Int) → after.data.dmem.loadInt preemptCountAddress 4 = some ((old-before.data.regs.get (.low .rsi .W32)).toNat : Int)))
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (initial : MachineState) (world : World)
    (pre : Pre_lookup c coverage preempt returnAddress initial world)
    (answer : Option (IndexOwner × PeerId)) (finalWorld : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, finalWorld)) :
    Eventually (guardedStep fetch (StackGuard initial.data.regs.rsp))
      (Post c coverage preempt returnAddress initial world answer finalWorld) initial := by
  have entryPC : initial.pc = Image.Lookup.entry := by obtain ⟨_, entry⟩ := pre; exact entry.pc
  cases initial with
  | mk s pc =>
    dsimp only at entryPC
    subst pc
    cases focused : c.focus.owner with
    | some owner =>
      exact guarded_forget (selected_execution fetch decoder tracePc traceCmp4 traceConstCmp4 traceConstCmp1 bhEnable
        c coverage preempt returnAddress s world pre owner focused answer finalWorld accepted) (fun _ h => h)
    | none =>
      exact guarded_forget (miss_execution fetch decoder tracePc traceCmp4 traceConstCmp4 bhEnable
        c coverage preempt returnAddress s world pre focused answer finalWorld accepted) (fun _ h => h)


#print axioms selected_execution
#print axioms miss_execution
#print axioms lookup_simulation
end Binary.Sequential.First
