import LookupHelperPrepared
import LookupResultSimulation

namespace Binary.LookupRelation
open Leanux Leanux.WG TrustBase LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Concrete result-region postcondition used by the final callback and
    return composition. No machine execution is assumed in this predicate. -/
def AfterResult (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (s : MachineData) (world : World) (v : View) (owner : IndexOwner) (current : Executed)
    (answer : Option PeerId) (helperFinal setWorld : World) (final : Executed) : Prop := ∃ af sourcePoints points,
      (∃ finalView, project c (LookupMirror.record setWorld .idxPeerAlive answer.isSome) = some finalView ∧ finalView.bucket = v.bucket) ∧
      (answer.isSome = true → LookupOutputNeeded v) ∧
      helperActive points = false ∧ lastHelperReturn points = none ∧
      final.machine = resultExit current.machine.data af ∧
      final.history = current.history ++ resultStates current.machine.data af ∧
      (∀ prior, ((MirrorHistory.peerGet c.focus.peer).run prior).run (helperWorld c world v) =
        .ok ((answer, prior ++ sourcePoints), helperFinal)) ∧
      LookupCoverage.Context.At ⟨coverage, preempt, v⟩ (512+preempt) final.machine.data.dmem ∧
      (answer.isSome = true → (final.machine.data.dmem.loadInt s.regs.rcx.toBitVec 8).isSome = true) ∧
      EqualOutside (InRange (ownerAddress c owner) 8) current.machine.data.dmem final.machine.data.dmem ∧
      observe c.rxSection final.history = .ok points ∧
      MatchesPoints (ExecutedCorrespondence.AtPoint (R c) c.rxSection final.history) points
        (helperSource c world v ++ sourcePoints ++ [⟨.returned "wg_peer_get_maybe_zero", helperFinal⟩] ++
          [⟨.decision .idxPeerAlive, LookupMirror.record setWorld .idxPeerAlive answer.isSome⟩]) ∧
      ExecutedCorrespondence.CutsAligned (R c) c.rxSection final.history
        (helperSource c world v ++ sourcePoints ++ [⟨.returned "wg_peer_get_maybe_zero", helperFinal⟩] ++
          [⟨.decision .idxPeerAlive, LookupMirror.record setWorld .idxPeerAlive answer.isSome⟩]) ∧
      R c final.history points final.machine (LookupMirror.record setWorld .idxPeerAlive answer.isSome)

/-- Actual selected-owner store region, with all separation derived from
    the original entry and the helper's preserved source bucket. -/
theorem result_from_helper (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (c : Config)
    (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (bucket helper current : Executed) (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (before : BeforeHelper c coverage preempt s world v bucket owner helper)
    (answer : Option PeerId) (helperFinal setWorld : World)
    (after : AfterHelper c coverage preempt s world v helper answer helperFinal current)
    (setRun : (owner.setPeerWord answer).run helperFinal = .ok ((), setWorld)) :
    historySteps fetch 4
      (AfterResult c coverage preempt s world v owner current answer helperFinal setWorld) current := by
  obtain ⟨callback, _, _, _, cbOwner, _, machine, _⟩ := before
  obtain ⟨ret, scratch, output, needed, ⟨afterView, projected, bucketEq, wordEq⟩, result, alive, ready, frame,
    sourcePoints, points, sourceRun, observed, returned, matched, aligned, related, _⟩ := after
  have pc : current.machine.pc = Image.Lookup.entry+0xba := ret.1
  have location : current.machine.data.regs.rbx.toBitVec = ownerAddress c owner := by
    rw [ret.2.2.1, machine]
    simpa only [peerCalled, Instrumentation.calledState, peerArgument, MachineData.setReg, Reg64s.set, Reg64s.set64] using cbOwner
  have bucketApart : ∀ other, project c helperFinal = some other → ∀ a, LookupBucketBytes c other a →
      ¬InRange (ownerAddress c owner) 8 a := by
    intro other otherProjected a read written
    have same : other = afterView := Option.some.inj (otherProjected.symm.trans projected)
    subst other
    apply entry.dataBucket a _ (.inl ⟨owner, focused, written⟩)
    simpa only [LookupBucketBytes, bucketEq] using read
  have countApart : ∀ a, LookupCountBytes c a → ¬InRange (ownerAddress c owner) 8 a := by
    intro a read written
    exact entry.ownerCount a read ⟨owner, focused, written⟩
  have run := result_simulation fetch agree c helperFinal setWorld current.machine.data current.history points
    (helperSource c world v ++ sourcePoints ++ [⟨.returned "wg_peer_get_maybe_zero", helperFinal⟩])
    (by simpa only [← pc] using related) observed matched aligned (by simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or, Option.map_some])
    (by simpa only [← pc] using returned) owner focused answer result location setRun bucketApart countApart
  have cursor : (⟨⟨current.machine.data, Image.Lookup.entry+0xba⟩, current.history⟩ : Executed) = current := by rw [← pc]
  rw [cursor] at run
  apply historySteps_mono fetch 4 _ _ _ _ run
  rintro final ⟨af, machine, recorded, full, matching, cuts, endpoint⟩
  have finalMemory : final.machine.data.dmem = (OwnerWord.stored current.machine.data).dmem := by
    rw [machine]
    rfl
  have memoryFrame : EqualOutside (InRange (ownerAddress c owner) 8) current.machine.data.dmem final.machine.data.dmem := by
    rw [finalMemory, ← location]
    exact OwnerWord.stored_frame _
  have context := LookupCoverage.state_frame ⟨coverage, preempt, v⟩ (512+preempt) _ _ ready _ memoryFrame (by
    intro a read written
    exact entry.dataService a read (.inl ⟨owner, focused, written⟩))
  have oldWord : afterView.ownerWord = some c.focus.peer := by
    rw [wordEq]
    simpa only [EntryFocus, focused] using entry.focus.2
  obtain ⟨next, nextRun, nextView, _, _⟩ := owner_set_project c helperFinal afterView owner c.focus.peer answer projected focused oldWord
  have same : next = setWorld := congrArg Prod.snd (Except.ok.inj (nextRun.symm.trans setRun))
  subst next
  have finalView : project c (LookupMirror.record setWorld .idxPeerAlive answer.isSome) =
      some {afterView with ownerWord := some answer} := by
    simpa only [LookupMirror.record, project_steps] using nextView
  refine ⟨af, sourcePoints, _, ⟨_, finalView, bucketEq⟩, needed, ?_, ?_, machine, recorded, sourceRun, context, ?_, memoryFrame, full, ?_, ?_, ?_⟩
  · simpa only [helperActive_decision] using helper_inactive_of_return points _ returned
  · simp [lastHelperReturn, decision]
  · intro live
    rw [finalMemory]
    exact storeInt_defined _ _ _ _ _ _ (output live)
  · simpa only [alive] using matching
  · simpa only [alive] using cuts
  · simpa only [alive] using endpoint

#print axioms result_from_helper
end Binary.LookupRelation
