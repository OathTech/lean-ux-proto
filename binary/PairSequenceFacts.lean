import PairSequenceCheck
import PairLookupAdequacy
import PairReplaceAdequacy
import PairRemoveAdequacy
import MemoryInvariant

namespace Binary.Pair.Sequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
set_option maxRecDepth 2048

structure InitialFacts (n : Names) (o : Offsets) (c : Context) (base : MachineState)
    (w : World) (ra : UInt64) : Prop where
  state : ∃ d, w.k.wg=some d ∧ Corresponds n o base.data.dmem d ∧
    Remove.ownership n o base.data.dmem=.ok (Remove.targetOwnership d)
  storage : storageCheck n o=true
  names : IndexLookup.interpretationCheck n=true
  frames : ∀ size ∈ stackSizes, Index.CallFacts n o c base ra size
  resident : ∀ owner a, (owner,a) ∈ n.owners →
    word base.data.dmem "sequence.kind" (a+o.kind) 4=.ok (ownerKind owner) ∧
    (∃ value, word base.data.dmem "sequence.next" (a+o.hash+o.next) 8=.ok value) ∧
    (∃ value, word base.data.dmem "sequence.index" (a+o.index) 4=.ok value)
  shapeApart : spansApart (IndexLookup.ownerSpans n ++ IndexLookup.countSpans n o) (IndexLookup.shapeSpans n o)=true
  countApart : spansApart (IndexLookup.ownerSpans n) (IndexLookup.countSpans n o)=true
  outputMapped : (base.data.dmem.loadInt base.data.regs.rcx.toBitVec 8).isSome=true
  outputApart : ∀ size ∈ stackSizes, spansApart (IndexLookup.outputSpan base)
    (storageSpans n o ++ callStack base size true ++ Trie.callServices c)=true
  callerApart : spansApart (Trie.callServices c) (callStack base 13 true)=true

theorem resident_facts {n o m} (checked : residentCheck n o m=.ok ()) :
    ∀ owner a, (owner,a) ∈ n.owners →
    word m "sequence.kind" (a+o.kind) 4=.ok (ownerKind owner) ∧
    (∃ value, word m "sequence.next" (a+o.hash+o.next) 8=.ok value) ∧
    (∃ value, word m "sequence.index" (a+o.index) 4=.ok value) := by
  unfold residentCheck at checked
  obtain ⟨_,checked,_⟩ := bind_ok checked
  intro owner a named
  obtain ⟨_,_,read⟩ := (mapM_ok checked).left (owner,a) named
  obtain ⟨kind,kindRead,read⟩ := bind_ok read
  obtain ⟨kindEq,read⟩ := check_ok _ _ _ _ read
  obtain ⟨next,nextRead,read⟩ := bind_ok read
  obtain ⟨index,indexRead,_⟩ := bind_ok read
  have equal : kind=ownerKind owner := eq_of_beq kindEq
  exact ⟨equal ▸ mapError_ok kindRead,⟨next,mapError_ok nextRead⟩,⟨index,mapError_ok indexRead⟩⟩

theorem initial_facts {n o c base w ra} (checked : initialCheck n o c base w ra=.ok ()) :
    InitialFacts n o c base w ra := by
  unfold initialCheck at checked
  obtain ⟨_,asserted,checked⟩ := bind_ok checked
  obtain ⟨d,device,related,storage,owned⟩ := remove_assert_ok asserted
  obtain ⟨names,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,frames,checked⟩ := bind_ok checked
  obtain ⟨_,resident,checked⟩ := bind_ok checked
  obtain ⟨apart,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨mapped,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨output,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨caller,_⟩ := check_ok _ _ _ _ checked
  have apart : spansApart (IndexLookup.ownerSpans n ++ IndexLookup.countSpans n o) (IndexLookup.shapeSpans n o)=true ∧
      spansApart (IndexLookup.ownerSpans n) (IndexLookup.countSpans n o)=true := by
    simpa only [Bool.and_eq_true] using apart
  refine ⟨⟨d,device,related,owned⟩,storage,names,?_,resident_facts resident,apart.1,apart.2,mapped,?_,caller⟩
  · intro size member
    obtain ⟨value,_,run⟩ := (mapM_ok frames).left size member
    cases value
    exact callFrameCheck_sound run
  · exact List.all_eq_true.mp output

/-- Resources retained across calls. Mapping and immutable tags are frames
relative to the initial allocation, separate from the source projection. -/
structure Ready (n : Names) (o : Offsets) (c : Context) (base : MachineState)
    (m : DataMem) (w : World) : Prop where
  state : ∃ d, w.k.wg=some d ∧ Corresponds n o m d ∧
    Remove.ownership n o m=.ok (Remove.targetOwnership d)
  coverage : ∀ b, (phase c b).CoverageAt m
  preempt : load32 m preemptCountAddress=some c.preempt
  pending : LookupPendingRead c.preempt → m.loadInt softirqPendingAddress 2=some 0
  mapped : ∀ a size, (base.data.dmem.loadInt a size).isSome=true → (m.loadInt a size).isSome=true
  kinds : KindFrame n o base.data.dmem m

theorem InitialFacts.ready {n o c base w ra} (facts : InitialFacts n o c base w ra) :
    Ready n o c base base.data.dmem w := by
  have frame := facts.frames 13 (by simp [stackSizes])
  exact ⟨facts.state,(fun b => by cases b; exact frame.coverage.1; exact frame.during),
    frame.coverage.2,frame.pending,(fun _ _ h => h),KindFrame.refl n o _⟩

theorem word_mapped {before after : DataMem} (mapped : ∀ a size,
    (before.loadInt a size).isSome=true → (after.loadInt a size).isSome=true)
    {path a size value} (read : word before path a size=.ok value) (newPath : String) :
    ∃ value, word after newPath a size=.ok value := by
  have initial := word_loadInt _ _ _ _ _ read
  have next := mapped (.ofNat 64 a) size (by rw [initial]; rfl)
  unfold word at read ⊢
  split at read
  next bound =>
    rw [ite_eq_left bound]
    cases bytes : after.loadBytes (.ofNat 64 a) size with
    | none => simp only [Mem.loadInt,bytes,Option.map_none,Option.isSome_none,Bool.false_eq_true] at next
    | some bs => exact ⟨_,rfl⟩
  next bad => cases read

#print axioms initial_facts
#print axioms word_mapped
end Binary.Pair.Sequence
