import PairInsertSequenceCaller
import PairInsertAdequacy

namespace Binary.Pair.InsertSequence
open Leanux Leanux.WG TrustBase CommonBitsCoverage Index
set_option maxRecDepth 2048

theorem install_resident {n o c base initialWorld ra current w config inputAt owner address}
    (facts : InitialFacts n o c base initialWorld ra config)
    (ready : Ready n o c base current w config inputAt)
    (named : addressOf n owner=.ok address) (pc arg2 arg3) :
    Insert.Resident n o (Sequence.install n base ra pc arg2 arg3 current).data.dmem owner address := by
  have next := Sequence.install_ready facts.previous ready.previous pc arg2 arg3
  have member := Remove.addressOf_ok named
  obtain ⟨kind,nextRead,indexRead⟩ := facts.previous.resident owner address member
  refine ⟨member,?_,?_,?_⟩
  · rw [next.kinds _ _ member]
    exact word_path kind _
  · obtain ⟨value,read⟩ := nextRead
    exact Sequence.word_mapped next.mapped read _
  · obtain ⟨value,read⟩ := indexRead
    exact Sequence.word_mapped next.mapped read _

/-- The complete insertion entry assertion is derived from the resources
retained after the preceding call, not supplied separately by the caller. -/
theorem insert_pre {n o c base initialWorld ra current w config inputAt fetch owner address}
    (facts : InitialFacts n o c base initialWorld ra config)
    (ready : Ready n o c base current w config inputAt)
    (coupling : RandomInputCoupling fetch config c.coverage (c.preempt+512)
      (Insert.codeEntry+0x79).toUInt64 inputAt)
    (named : addressOf n owner=.ok address) :
    Insert.Pre n o c (Sequence.install n base ra Insert.codeEntry address 0 current) w owner ra config := by
  have next := install_ready facts ready coupling Insert.codeEntry address 0
  have frame := install_frame facts ready facts.frame Insert.codeEntry address 0
  refine ⟨?_,(install_provider facts ready coupling Insert.codeEntry address 0).checked⟩
  have args : ((Sequence.install n base ra Insert.codeEntry address 0 current).pc.toBitVec.toNat==Insert.entry &&
      (Sequence.install n base ra Insert.codeEntry address 0 current).data.regs.rdi.toNat==n.table &&
      (Sequence.install n base ra Insert.codeEntry address 0 current).data.regs.rsi.toNat==address)=true := by
    have member := Remove.addressOf_ok named
    have bound := entry_bound facts.previous.storage member
    have positive := (storage_bounds facts.previous.storage (entry_storage member)).1
    have table := storage_bounds facts.previous.storage (table_storage n o)
    simp only [Sequence.install,Bool.and_eq_true,beq_iff_eq]
    exact ⟨⟨rfl,Nat.mod_eq_of_lt (by omega)⟩,Nat.mod_eq_of_lt (by omega)⟩
  have nested : (Context.mk c.coverage (c.preempt+1024)).CoverageAt
      (Sequence.install n base ra Insert.codeEntry address 0 current).data.dmem := by
    rw [Insert.nested_coverage c facts.frame.hardirq facts.nestedHardirq]
    exact next.previous.coverage true
  apply Insert.boundary_of_parts (next.previous.asserted facts.previous.storage) named args
    (install_resident facts ready named Insert.codeEntry address 0)
    (Insert.FrameFacts.mk frame nested facts.nestedHardirq next.nestedPending facts.nested_apart)
  obtain ⟨records,supplied,_⟩ := ready.input
  rw [supplied]
  rfl

#print axioms insert_pre
end Binary.Pair.InsertSequence
