import PairInsertSequenceGeometry
import PairInsertCheckComplete
import PairInsertProviderComplete

namespace Binary.Pair.InsertSequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
set_option maxRecDepth 2048

/-- Caller installation preserves the private input provider as well as the
shared index heap. Only the return slot is written. -/
theorem install_ready {n o c base initialWorld ra current w config inputAt fetch}
    (facts : InitialFacts n o c base initialWorld ra config)
    (ready : Ready n o c base current w config inputAt)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512)
      ((Int64.ofNat Insert.entry)+0x79).toUInt64 inputAt) (pc arg2 arg3) :
    Ready n o c base (Sequence.install n base ra pc arg2 arg3 current) w config inputAt := by
  have frame := Sequence.install_writes n o c base ra pc arg2 arg3 current
  have privateFrame := facts.private_frame frame
  have next := Sequence.install_ready facts.previous ready.previous pc arg2 arg3
  refine ⟨next,⟨?_,ready.provider.privilege,ready.provider.direction,?_⟩,?_,?_⟩
  · rw [←RandomProvider.check_frame privateFrame]
    exact ready.provider.privateCheck
  · intro a size prior
    exact storeInt_defined _ _ _ _ _ _ (ready.provider.mapped a size prior)
  · intro needed
    have frame : EqualOutside (Writes n o c base config) current.data.dmem
        (Sequence.install n base ra pc arg2 arg3 current).data.dmem :=
      fun a outside => frame a (fun written => outside (existing_writes written))
    exact (facts.pending_frame frame needed).symm.trans (ready.nestedPending needed)
  · obtain ⟨records,supplied,input⟩ := ready.input
    exact ⟨records,supplied,coupling.frame _ _ records privateFrame input⟩

/-- A previously checked reservation can be re-established over the retained
memory without testing or assuming a future callee execution. -/
theorem install_frame {n o c base initialWorld ra current w config inputAt size}
    (facts : InitialFacts n o c base initialWorld ra config)
    (ready : Ready n o c base current w config inputAt)
    (prior : Index.CallFacts n o c base ra size) (pc arg2 arg3) :
    Index.CallFacts n o c (Sequence.install n base ra pc arg2 arg3 current) ra size := by
  have next := Sequence.install_ready facts.previous ready.previous pc arg2 arg3
  refine ⟨⟨prior.entry.1,?_⟩,?_,⟨next.coverage false,next.preempt⟩,next.coverage true,
    prior.hardirq,next.pending,prior.heapApart,prior.serviceApart,prior.bufferApart,prior.preemptApart⟩
  · exact load64_store _ _ ra.toBitVec
  · intro i hi
    exact next.mapped _ _ (prior.stack i hi)

theorem install_provider {n o c base initialWorld ra current w config inputAt fetch}
    (facts : InitialFacts n o c base initialWorld ra config)
    (ready : Ready n o c base current w config inputAt)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512)
      ((Int64.ofNat Insert.entry)+0x79).toUInt64 inputAt) (pc arg2 arg3) :
    Insert.ProviderFacts n o c (Sequence.install n base ra pc arg2 arg3 current) ra config := by
  have next := install_ready facts ready coupling pc arg2 arg3
  exact ⟨install_frame facts ready facts.provider.wide pc arg2 arg3,
    next.provider.privilege,next.provider.direction,facts.provider.capacity,next.provider.privateCheck,
    facts.provider.privateApart,facts.provider.pendingApart⟩

#print axioms install_ready
#print axioms install_provider
end Binary.Pair.InsertSequence
