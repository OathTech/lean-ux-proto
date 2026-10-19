import SourceAdapter
import LookupPost
import LookupCutFrames
import LookupSelectedExecution
import LookupLiveFinish
import LookupClearFinish

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Selected-owner execution all the way to the original caller. NULL,
    dead and live helper results use their actual compiled tail paths. -/
theorem selected_execution (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (traceCmp : TraceCmp4Contract fetch) (traceConstCmp : TraceConstCmp4Contract fetch)
    (traceByte : TraceConstCmp1Contract fetch) (bh : BhEnableContract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (ra : UInt64)
    (s : MachineData) (world : World)
    (pre : Pre_lookup c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (answer : Option (IndexOwner × PeerId)) (finalWorld : World)
    (accepted : (Source.indexLookup c.kinds c.query).run world = .ok (answer, finalWorld)) :
    Eventually (historyStep fetch)
      (LookupPost c coverage preempt ra ⟨s, Image.Lookup.entry⟩ world answer finalWorld)
      ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  apply eventually_trans (historyStep fetch) _ _ _
    (selected_through_result fetch agree tracePc traceCmp traceConstCmp traceByte c coverage preempt ra s world pre
      owner focused answer finalWorld accepted)
  rintro result ⟨v, bucket, helper, current, helperAnswer, helperFinal, setWorld, points, source,
    entry, bucketAt, before, after, resultAt, answerEq, finalEq, sourceRun, observed, matched, aligned, related,
    latest, inactive, noReturn⟩
  have frames := result_cut_frames c coverage preempt ra s world v entry bucket helper current result owner focused
    bucketAt before helperAnswer helperFinal setWorld after resultAt
  have prepared := selected_result_ready c coverage preempt ra s world v entry bucket helper current result owner focused
    bucketAt before helperAnswer helperFinal setWorld after resultAt
  obtain ⟨saved, frame, ready, output, ownerReg, peerReg, pc⟩ := prepared
  obtain ⟨_, _, _, view, needed, _, _, _, _, _, _, mapped, _⟩ := resultAt
  have sourceView : ∃ view, project c finalWorld = some view ∧ view.bucket = v.bucket := by
    simpa only [finalEq] using view
  cases helperAnswer with
  | none =>
    have run := clear_finish fetch agree tracePc bh c coverage preempt ra s world v entry result
      (by simpa only [Option.isSome_none, Bool.false_eq_true, ite_false] using pc)
      finalWorld sourceView saved ready frame points source related observed matched aligned latest inactive noReturn frames
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨ret, zero, frame, full, matching, cuts, endpoint, cutFrames, coverageAt, countAt, ended⟩
    refine ⟨ret, ?_, v, _, _, entry, frame, sourceRun, full, matching, cuts, endpoint, cutFrames, coverageAt, countAt,
      pending_from_frame c coverage preempt ra s final.machine.data world v entry frame, ended⟩
    simpa only [answerEq, Option.map_none, LookupResult] using zero
  | some pid =>
    have run := live_finish fetch agree tracePc bh c coverage preempt ra s world v entry result
      (by simpa only [Option.isSome_some, ite_true] using pc)
      finalWorld sourceView saved ready frame output (needed rfl) (mapped rfl)
      points source related observed matched aligned latest inactive noReturn frames
    apply eventually_weaken (historyStep fetch) _ _ _ _ run
    rintro final ⟨ret, value, outValue, frame, full, matching, cuts, endpoint, cutFrames, coverageAt, countAt, ended⟩
    refine ⟨ret, ?_, v, _, _, entry, frame, sourceRun, full, matching, cuts, endpoint, cutFrames, coverageAt, countAt,
      pending_from_frame c coverage preempt ra s final.machine.data world v entry frame, ended⟩
    simp only [answerEq, Option.map_some, LookupResult]
    constructor
    · rw [value]; exact ownerReg
    · rw [outValue]
      have h := congrArg BitVec.toNat peerReg
      simpa only [OwnerWord.pointer, UInt64.toNat_toBitVec] using congrArg (fun n : Nat => some (n : Int)) h

#print axioms selected_execution
end Binary.LookupRelation
