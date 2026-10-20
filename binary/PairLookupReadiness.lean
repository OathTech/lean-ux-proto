import PairLookupPre

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase LookupRelation CommonBitsCoverage Index
set_option maxRecDepth 2048

/-- M1 exports the buffer when its path uses it. The common entry also
carried the unused phase's readiness; recover that by the actual write frame.
This is needed when the next call visits a different bucket or a mutator. -/
theorem coverage_after {n o coverage s w d query kinds ra after}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (covered : LookupCoverageAt coverage.coverage coverage.preempt (callView (callConfig n w d query kinds) d) after)
    (frame : EqualOutside (LookupWrites (callConfig n w d query kinds) coverage.coverage coverage.preempt s.data
      (callView (callConfig n w d query kinds) d)) s.data.dmem after) :
    ∀ b, (phase coverage b).CoverageAt after := by
  intro b
  let g := facts.frame.geometry
  let c := callConfig n w d query kinds
  let v := callView c d
  have prior : (phase coverage b).CoverageAt s.data.dmem := by
    cases b
    · exact facts.frame.coverage.1
    · exact facts.frame.during
  apply coverage_metadata_frame (phase coverage b) s.data.dmem after prior _ frame
  · intro a read written
    have metadata := phase_metadata coverage b a read
    rcases written with stack | buffer | preempt | data | ⟨needed,output⟩
    · exact g.serviceStack a (.inl (.inl metadata)) stack
    · exact g.bufferMetadata a (coverage_writes buffer) metadata
    · exact g.preemptMetadata a metadata preempt
    · exact g.heapService a (data_heap facts.related facts.names a data) (.inl (.inl metadata))
    · exact facts.output_services needed a output (.inl (.inl metadata))
  · intro needed
    by_cases active : LookupBufferNeeded coverage.coverage coverage.preempt v
    · exact (covered.2.2.2 active).2.2
    · apply Kcov.buffer_frame coverage.coverage s.data.dmem after (prior.2.2.2 needed).2.2 _ frame
      intro a read written
      have either : coverage.Needed ∨ (Context.mk coverage.coverage (coverage.preempt+512)).Needed := by
        cases b
        · exact .inl needed
        · exact .inr needed
      have service : AllowedipsServiceBytes coverage.coverage coverage.preempt a := .inr ⟨either,read⟩
      rcases written with stack | buffer | preempt | data | ⟨outNeeded,output⟩
      · exact g.serviceStack a (.inl service) stack
      · exact active buffer.1
      · rcases read with header | buffer
        · exact g.preemptHeader a either header preempt
        · exact g.bufferPreempt a ⟨either,buffer⟩ preempt
      · exact g.heapService a (data_heap facts.related facts.names a data) (.inl service)
      · exact facts.output_services outNeeded a output (.inl service)

#print axioms coverage_after
end Binary.Pair.IndexLookup
