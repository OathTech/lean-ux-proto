import SequentialHelper
import LookupResultPrepared

namespace Binary.Sequential
open Leanux Leanux.WG TrustBase LookupRelation LookupHistory LookupObservation
local instance : Labels := Image.linkedLabels

/-- Both sides have committed the owner update at this proof-only point. -/
def AfterResult (c : Config) (coverage : KcovLayout) (preempt : BitVec 32)
    (s : MachineData) (world : World) (v : View) (owner : IndexOwner) (current : Executed)
    (answer : Option PeerId) (helperFinal setWorld : World) (final : Executed) : Prop := ∃ af,
      (∃ finalView, project c (LookupMirror.record setWorld .idxPeerAlive answer.isSome) = some finalView ∧ finalView.bucket = v.bucket) ∧
      (answer.isSome = true → LookupOutputNeeded v) ∧
      final.machine = resultExit current.machine.data af ∧
      LookupCoverage.Context.At ⟨coverage, preempt, v⟩ (512+preempt) final.machine.data.dmem ∧
      (answer.isSome = true → (final.machine.data.dmem.loadInt s.regs.rcx.toBitVec 8).isSome = true) ∧
      EqualOutside (InRange (ownerAddress c owner) 8) current.machine.data.dmem final.machine.data.dmem ∧
      Related c final.machine (LookupMirror.record setWorld .idxPeerAlive answer.isSome)

theorem result_from_helper (fetch : Int64 → Option Decoded)
    (agree : AnchoredDecoderAgreement fetch) (c : Config)
    (coverage : KcovLayout) (preempt : BitVec 32) (returnAddress : UInt64)
    (s : MachineData) (world : World) (v : View)
    (entry : LookupEntry c coverage preempt returnAddress ⟨s, Image.Lookup.entry⟩ world v)
    (bucket helper current : Executed) (owner : IndexOwner) (focused : c.focus.owner = some owner)
    (before : BeforeHelper c coverage preempt s world v bucket owner helper)
    (answer : Option PeerId) (helperFinal setWorld : World)
    (after : AfterHelper c coverage preempt s world v helper answer helperFinal current)
    (setRun : (Source.setPeerWord owner answer).run helperFinal = .ok ((), setWorld)) :
    historySteps fetch 4
      (AfterResult c coverage preempt s world v owner current answer helperFinal setWorld) current := by
  obtain ⟨callback, _, _, _, cbOwner, _, machine, _⟩ := before
  obtain ⟨ret, scratch, output, needed, ⟨afterView, projected, bucketEq, wordEq⟩, result, alive, ready, frame,
    related⟩ := after
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
  have represented : At c current.machine.data.dmem afterView := by
    obtain ⟨other, projection, physical⟩ := related
    have eq : other = afterView := Option.some.inj (projection.symm.trans projected)
    simpa only [eq] using physical
  have ownerField : OwnerWord.Field c.peers current.machine.data.dmem (ownerAddress c owner) c.focus.peer := by
    have h := represented.2.2.1
    simp only [focused] at h
    obtain ⟨word, wordAt, field⟩ := h
    have original : afterView.ownerWord = some c.focus.peer := by
      rw [wordEq]
      simpa only [EntryFocus, focused] using entry.focus.2
    have eq : word = c.focus.peer := Option.some.inj (wordAt.symm.trans original)
    simpa only [eq] using field
  have run := result_history fetch agree c.peers current.machine.data c.focus.peer
    (by simpa only [location] using ownerField) current.history
  have cursor : (⟨⟨current.machine.data, Image.Lookup.entry+0xba⟩, current.history⟩ : Executed) = current := by rw [← pc]
  rw [cursor] at run
  apply historySteps_mono fetch 4 _ _ _ _ run
  rintro final ⟨af, machine, recorded⟩
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
  refine ⟨af, ⟨_, finalView, bucketEq⟩, needed, machine, context, ?_, memoryFrame, ?_⟩
  · intro live
    rw [finalMemory]
    exact storeInt_defined _ _ _ _ _ _ (output live)
  · refine ⟨_, finalView, ?_⟩
    exact represented.owner_update owner focused answer memoryFrame (bucketApart afterView projected) countApart (by
      rw [finalMemory, ← location]
      exact OwnerWord.stored_field _ _ _ result)

#print axioms result_from_helper
end Binary.Sequential
