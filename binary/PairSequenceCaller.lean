import PairSequenceFacts
import PairCheckComplete

namespace Binary.Pair.Sequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
set_option maxRecDepth 2048

theorem return_live (base : MachineState) (a : BitVec 64)
    (inside : InRange base.data.regs.rsp.toBitVec 8 a) : LiveStack base 13 a :=
  Stack.inside _ _ 0 (by omega) a (by simpa only [Stack.slot,Nat.mul_zero,BitVec.sub_zero] using inside)

theorem InitialFacts.return_service {n o c base w ra}
    (facts : InitialFacts n o c base w ra) (a : BitVec 64)
    (read : AllowedipsServiceBytes c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a) :
    ¬InRange base.data.regs.rsp.toBitVec 8 a := by
  intro inside
  exact spansApart_disjoint facts.callerApart (Trie.callServices_cover c) (live_cover base 13)
    a read (return_live base a inside)

/-- Explicit caller setup preserves all retained heap and service state.
Only the return slot is written; initial resource geometry justifies it. -/
theorem install_ready {n o c base initialWorld ra current w}
    (facts : InitialFacts n o c base initialWorld ra)
    (ready : Ready n o c base current.data.dmem w) (pc arg2 arg3) :
    Ready n o c base (install n base ra pc arg2 arg3 current).data.dmem w := by
  let after := (install n base ra pc arg2 arg3 current).data.dmem
  have frame : EqualOutside (InRange base.data.regs.rsp.toBitVec 8) current.data.dmem after :=
    storeInt_frame _ _ _ _
  have geometry := (facts.frames 13 (by simp [stackSizes])).geometry
  have heap : StorageFrame n o current.data.dmem after := by
    apply StorageFrame.of_execution frame
    intro span member a inside written
    exact geometry.heapLive a ⟨span,member,inside⟩ (return_live base a written)
  obtain ⟨d,device,related,owned⟩ := ready.state
  have layout := (validate_basic (reconstruct_components related).1).1
  have state := state_frame c current.data.dmem after ⟨ready.coverage false,ready.preempt⟩ _ frame
    (fun a read => facts.return_service a (AllowedipsCoverage.bytes_before _ _ a read))
  refine ⟨⟨d,device,heap.reconstruct related,?_⟩,?_,state.2,?_,?_,ready.kinds.trans (heap.kinds layout)⟩
  · rw [←heap.ownership layout]
    exact owned
  · intro b
    exact coverage_frame (phase c b) _ _ (ready.coverage b) _ frame
      (fun a read => facts.return_service a (phase_bytes c b a read))
  · intro needed
    have same := frame.loadInt softirqPendingAddress 2 (by
      intro i hi
      exact facts.return_service _ (.inl (.inl (.inr (.inr (.inr (.inr ⟨needed,i,hi,rfl⟩)))))))
    exact same.symm.trans (ready.pending needed)
  · intro a size prior
    exact storeInt_defined _ _ _ _ _ _ (ready.mapped a size prior)

theorem install_frame {n o c base initialWorld ra current w}
    (facts : InitialFacts n o c base initialWorld ra)
    (ready : Ready n o c base current.data.dmem w) (pc arg2 arg3 size)
    (sizeAt : size ∈ stackSizes) :
    Index.CallFacts n o c (install n base ra pc arg2 arg3 current) ra size := by
  have prior := facts.frames size sizeAt
  have next := install_ready facts ready pc arg2 arg3
  refine ⟨⟨prior.entry.1,?_⟩,?_,⟨next.coverage false,next.preempt⟩,next.coverage true,
    prior.hardirq,next.pending,prior.heapApart,prior.serviceApart,prior.bufferApart,prior.preemptApart⟩
  · exact load64_store _ _ ra.toBitVec
  · intro i hi
    exact next.mapped _ _ (prior.stack i hi)

theorem Ready.asserted {n o c base m w} (ready : Ready n o c base m w)
    (storage : storageCheck n o=true) : Remove.assertAt n o m w=.ok () := by
  obtain ⟨d,device,related,owned⟩ := ready.state
  exact remove_assert_of_parts device storage related owned

theorem Ready.newReady {n o c base initialWorld ra m w d kid a}
    (facts : InitialFacts n o c base initialWorld ra) (ready : Ready n o c base m w)
    (named : (.keypair kid,a) ∈ n.owners)
    (absent : d.indexTable.any (·.owner==.keypair kid)=false) : Replace.NewReady o m d kid a := by
  obtain ⟨kind,next,index⟩ := facts.resident (.keypair kid) a named
  refine ⟨absent,?_,?_,?_⟩
  · rw [ready.kinds _ _ named]
    exact word_path kind _
  · obtain ⟨value,read⟩ := next
    exact word_mapped ready.mapped read _
  · obtain ⟨value,read⟩ := index
    exact word_mapped ready.mapped read _

#print axioms install_ready
#print axioms install_frame
end Binary.Pair.Sequence
