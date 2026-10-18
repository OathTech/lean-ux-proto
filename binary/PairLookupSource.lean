import PairLookupSourceFrame

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG LookupRelation
set_option maxRecDepth 2048

theorem helper_source_frame {c : Config} {w final : World} {d : Device} {answer : Option PeerId}
    (device : w.k.wg=some d)
    (present : ∀ id, c.focus.peer=some id → ∃ peer, d.peers.get? id=some peer)
    (accepted : (WG.peerGetMaybeZero c.focus.peer).run w=.ok (answer,final)) :
    ∃ after, final.k.wg=some after ∧ SourceFrame c d after ∧
      (∀ owner, OwnerWord.value after owner=OwnerWord.value d owner) ∧
      (answer=none ∨ answer=c.focus.peer) := by
  cases focus : c.focus.peer with
  | none =>
    rw [focus,PeerMirror.peer_null_run] at accepted
    have answerEq := congrArg Prod.fst (Except.ok.inj accepted)
    have equal := congrArg Prod.snd (Except.ok.inj accepted)
    dsimp only at equal
    rw [←equal]
    exact ⟨d,device,SourceFrame.refl c d,fun _ => rfl,.inl answerEq.symm⟩
  | some id =>
    obtain ⟨peer,found⟩ := present id focus
    rw [focus] at accepted
    have result := PeerMirror.accepted_peer_result id w final answer d peer device found accepted
    rw [result.2]
    by_cases zero : peer.refcount=0
    · refine ⟨d,?_,SourceFrame.refl c d,fun _ => rfl,.inl (by simpa only [zero,↓reduceIte] using result.1)⟩
      simpa [PeerMirror.peerFinal,zero,LookupMirror.record,PeerMirror.countRecords,PeerMirror.recordCmp] using device
    · refine ⟨{d with peers := d.peers.insert id {peer with refcount := peer.refcount+1}},?_,
        SourceFrame.count found focus _,(fun owner => owner_value_count_update d id peer _ found owner),
        .inr (by simpa only [zero,↓reduceIte,focus] using result.1)⟩
      simp [PeerMirror.peerFinal,zero,LookupMirror.record,PeerMirror.countRecords,PeerMirror.recordCmp,device]

/-- This frame follows the actual accepted mirror function. It covers the
NULL and zero-count branches; positive-count bounds come only from acceptance. -/
theorem lookup_source_frame {n o coverage s w d query kinds ra answer final}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (accepted : (WG.indexLookup kinds query).run w=.ok (answer,final)) :
    ∃ after, final.k.wg=some after ∧ SourceFrame (callConfig n w d query kinds) d after ∧
      ∀ owner, (callConfig n w d query kinds).focus.owner=some owner → ∀ value,
        OwnerWord.value after owner=some value → value=none ∨ value=(callConfig n w d query kinds).focus.peer := by
  let c := callConfig n w d query kinds
  let v := callView c d
  cases focus : c.focus.owner with
  | none =>
    obtain ⟨_,finalEq⟩ := lookup_no_owner_accepted c coverage.coverage coverage.preempt ra s w v facts.entry
      focus answer final accepted
    rw [finalEq,LookupSearch.result_world]
    refine ⟨d,facts.device,SourceFrame.refl c d,?_⟩
    intro owner selected
    cases selected
  | some owner =>
    obtain ⟨helperAnswer,helperFinal,middle,points,helperAccepted,_,continuation,_⟩ :=
      lookup_accepts_helper c coverage.coverage coverage.preempt ra s w v facts.entry owner focus answer final accepted
    obtain ⟨setWorld,setRun,_,finalEq,_⟩ := afterHelper_accepted owner helperAnswer middle points helperFinal final answer continuation
    have device : (helperWorld c w v).k.wg=some d := by
      rw [helperWorld,LookupSearch.result_world]
      exact facts.device
    obtain ⟨after,deviceAfter,helperFrame,words,allowed⟩ := helper_source_frame device
      (fun id selected => call_peer facts.related selected) helperAccepted
    obtain ⟨old,oldPresent⟩ := selected_word facts.related focus
    obtain ⟨result,resultDevice,setFrame,stored⟩ := setter_frame deviceAfter ((words owner).trans oldPresent) focus setRun
    rw [finalEq]
    refine ⟨result,resultDevice,helperFrame.trans setFrame,?_⟩
    intro chosen chosenFocus value valueAt
    have ownerEq := Option.some.inj chosenFocus
    subst chosen
    have wordEq := Option.some.inj (valueAt.symm.trans stored)
    rw [wordEq]
    exact allowed

#print axioms lookup_source_frame
end Binary.Pair.IndexLookup
