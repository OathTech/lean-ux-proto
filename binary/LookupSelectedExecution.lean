import LookupAcceptedSource
import LookupResultPrepared

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Selected-owner execution from the witnessed lookup entry through the
    result decision. The matched source prefix is the actual accepted lookup
    with only its outer return marker remaining. NULL and dead peers are
    included; all machine premises are derived from Pre_lookup. -/
theorem selected_through_result (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (tracePc : TracePcContract fetch)
    (traceCmp : TraceCmp4Contract fetch) (traceConstCmp : TraceConstCmp4Contract fetch)
    (traceByte : TraceConstCmp1Contract fetch)
    (c : Config) (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World)
    (pre : Pre_lookup c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world)
    (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (answer : Option (IndexOwner × PeerId)) (finalWorld : World)
    (accepted : (indexLookup c.kinds c.query).run world = .ok (answer, finalWorld)) :
    Eventually (historyStep fetch) (fun final =>
      ∃ v bucket helper current helperAnswer helperFinal setWorld points source,
        LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v ∧
        AfterBucket c world s coverage preempt v bucket ∧
        BeforeHelper c coverage preempt s world v bucket owner helper ∧
        AfterHelper c coverage preempt s world v helper helperAnswer helperFinal current ∧
        AfterResult c coverage preempt s world v owner current helperAnswer helperFinal setWorld final ∧
        answer = helperAnswer.map (fun pid => (owner, pid)) ∧
        finalWorld = LookupMirror.record setWorld .idxPeerAlive helperAnswer.isSome ∧
        ((MirrorHistory.lookup c.kinds c.query).run []).run world =
          .ok ((answer, source ++ [⟨.returned "wg_index_hashtable_lookup", finalWorld⟩]), finalWorld) ∧
        observe c.rxSection final.history = .ok points ∧
        MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) points source ∧
        ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history source ∧
        R c final.history points final.machine finalWorld ∧
        source.getLast?.map (·.world) = some finalWorld ∧
        helperActive points = false ∧ lastHelperReturn points = none)
      ⟨⟨s, Image.Lookup.entry⟩, [⟨s, Image.Lookup.entry⟩]⟩ := by
  obtain ⟨v, entry⟩ := pre
  obtain ⟨helperAnswer, helperFinal, middle, sourcePoints, helperAccepted, calledRun, continuation, fullSource⟩ :=
    lookup_accepts_helper c coverage preempt returnAddress _ world v entry owner focused answer finalWorld accepted
  obtain ⟨setWorld, setRun, answerEq, finalEq, sourceEq⟩ :=
    afterHelper_accepted owner helperAnswer middle sourcePoints helperFinal finalWorld answer continuation
  apply eventually_trans (historyStep fetch) _ _ _
    (start_from_entry fetch agree tracePc c coverage preempt returnAddress s world v entry)
  intro started startedAt
  apply eventually_trans (historyStep fetch) _ _ _
    (header_from_started fetch agree c coverage preempt returnAddress s world v entry started startedAt)
  intro head headAt
  apply eventually_trans (historyStep fetch) _ _ _
    (bucket_from_head fetch agree tracePc traceCmp traceConstCmp c coverage preempt returnAddress s world v entry head headAt)
  intro bucket bucketAt
  apply eventually_trans (historyStep fetch) _ _ _
    (helper_call_from_bucket fetch agree tracePc c coverage preempt returnAddress s world v entry bucket bucketAt owner focused)
  intro helper before
  apply eventually_trans (historyStep fetch) _ _ _
    (helper_from_call fetch agree tracePc traceConstCmp traceByte c coverage preempt returnAddress s world v entry bucket helper
      bucketAt owner focused before helperAnswer helperFinal helperAccepted)
  intro current after
  have run := historySteps_eventually fetch 4 _ _
    (result_from_helper fetch agree c coverage preempt returnAddress s world v entry bucket helper current owner focused
      before helperAnswer helperFinal setWorld after setRun)
  apply eventually_weaken (historyStep fetch) _ _ _ _ run
  intro final afterResult
  obtain ⟨af, helperPoints, points, finalView, needed, inactive, noReturn, machine, recorded, helperRun, ready, output, frame, observed, matched, aligned, related⟩ := afterResult
  have helperLogged := MirrorHistory.called_run "wg_peer_get_maybe_zero" (MirrorHistory.peerGet c.focus.peer)
    (helperWorld c world v) helperFinal helperAnswer helperPoints helperRun
    (LookupSearch.result c.kinds c.query v.bucket [sourceEntry world] world).1.2
  have same := Except.ok.inj (helperLogged.symm.trans calledRun)
  have middleEq := congrArg (fun p => p.1.2) same
  dsimp only at middleEq
  let source := helperSource c world v ++ helperPoints ++ [⟨.returned "wg_peer_get_maybe_zero", helperFinal⟩] ++
    [⟨.decision .idxPeerAlive, LookupMirror.record setWorld .idxPeerAlive helperAnswer.isSome⟩]
  refine ⟨v, bucket, helper, current, helperAnswer, helperFinal, setWorld, points, source,
    entry, bucketAt, before, after, ?_, answerEq, finalEq, ?_, observed, matched, aligned, ?_, ?_, inactive, noReturn⟩
  · exact ⟨af, helperPoints, points, finalView, needed, inactive, noReturn, machine, recorded, helperRun, ready, output, frame, observed, matched, aligned, related⟩
  · rw [sourceEq, ← middleEq, finalEq] at fullSource
    simpa only [source, helperSource, finalEq] using fullSource
  · simpa only [finalEq] using related
  · simp only [source, List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some, finalEq]

#print axioms selected_through_result
end Binary.LookupRelation
