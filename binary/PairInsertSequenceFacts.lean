import PairInsertSequenceCheck
import PairSequenceFacts
import PairInsertProviderState

namespace Binary.Pair.InsertSequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index

structure InitialFacts (n : Names) (o : Offsets) (c : Context) (base : MachineState)
    (w : World) (ra : UInt64) (config : RandomProvider.Config) : Prop where
  previous : Sequence.InitialFacts n o c base w ra
  frame : Index.CallFacts n o c base ra 7
  provider : Insert.ProviderFacts n o c base ra config
  nested : (Context.mk c.coverage (c.preempt+1024)).CoverageAt base.data.dmem
  nestedHardirq : (c.preempt+1024) &&& 0x000f0000=0
  nestedPending : LookupPendingRead (c.preempt+512) → base.data.dmem.loadInt softirqPendingAddress 2=some 0
  pendingApart : LookupPendingRead (c.preempt+512) →
    spansApart [(softirqPendingAddress.toNat,2)] (pendingProtected n o c base config)=true
  outputApart : spansApart config.blocks (IndexLookup.outputSpan base)=true
  input : w.hidden.isSome=true

theorem initial_facts {n o c base w ra config}
    (checked : initialCheck n o c base w ra config=.ok ()) : InitialFacts n o c base w ra config := by
  unfold initialCheck at checked
  obtain ⟨u,previous,checked⟩ := bind_ok checked
  cases u
  obtain ⟨u,frame,checked⟩ := bind_ok checked
  cases u
  obtain ⟨u,provider,checked⟩ := bind_ok checked
  cases u
  obtain ⟨nested,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨hardirq,checked⟩ := check_ok _ _ _ _ checked
  by_cases needed : LookupPendingRead (c.preempt+512)
  · simp only [needed,↓reduceIte] at checked
    obtain ⟨pending,checked⟩ := check_ok _ _ _ _ checked
    obtain ⟨apart,checked⟩ := check_ok _ _ _ _ checked
    obtain ⟨output,checked⟩ := check_ok _ _ _ _ checked
    obtain ⟨input,_⟩ := check_ok _ _ _ _ checked
    exact ⟨Sequence.initial_facts previous,Index.callFrameCheck_sound frame,
      Insert.providerCheck_sound provider,Trie.coverageDataCheck_sound nested,eq_of_beq hardirq,
      fun _ => eq_of_beq pending,fun _ => apart,output,input⟩
  · simp only [needed,↓reduceIte] at checked
    obtain ⟨output,checked⟩ := check_ok _ _ _ _ checked
    obtain ⟨input,_⟩ := check_ok _ _ _ _ checked
    exact ⟨Sequence.initial_facts previous,Index.callFrameCheck_sound frame,
      Insert.providerCheck_sound provider,Trie.coverageDataCheck_sound nested,eq_of_beq hardirq,
      fun h => False.elim (needed h),fun h => False.elim (needed h),output,input⟩

/-- The existing exact index projection plus physical frames and the remaining
supplied input. No future precondition or execution occurs in this invariant. -/
structure Ready (n : Names) (o : Offsets) (c : Context) (base current : MachineState)
    (w : World) (config : RandomProvider.Config) (inputAt : DataMem → List HiddenRecord → Prop) : Prop where
  previous : Sequence.Ready n o c base current.data.dmem w
  provider : Insert.ProviderState config c base current
  nestedPending : LookupPendingRead (c.preempt+512) → current.data.dmem.loadInt softirqPendingAddress 2=some 0
  input : ∃ records, w.hidden=some records ∧ inputAt current.data.dmem records

theorem InitialFacts.ready {n o c base w ra config inputAt records}
    (facts : InitialFacts n o c base w ra config) (supplied : w.hidden=some records)
    (input : inputAt base.data.dmem records) : Ready n o c base base w config inputAt :=
  ⟨facts.previous.ready,Insert.ProviderState.initial facts.provider,facts.nestedPending,⟨records,supplied,input⟩⟩

#print axioms initial_facts
#print axioms InitialFacts.ready
end Binary.Pair.InsertSequence
