import PairInsertProviderState
import PairInsertState

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Instrumentation

theorem random_metadata {c : Context} {a : BitVec 64}
    (read : RandomMetadata c.coverage (c.preempt+512) a) :
    AllowedipsMetadata c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a := by
  rcases read with current | count | soft | mode | buffer
  · exact .inl (AllowedipsCoverage.metadata_during _ _ _ (.inl current))
  · exact .inr count
  · exact .inl (AllowedipsCoverage.metadata_during _ _ _ (.inr (.inl soft)))
  · exact .inl (AllowedipsCoverage.metadata_during _ _ _ (.inr (.inr (.inl mode))))
  · exact .inl (AllowedipsCoverage.metadata_during _ _ _ (.inr (.inr (.inr buffer))))

theorem random_buffer_writes {c : Context} {a : BitVec 64}
    (capacity : (Context.mk c.coverage (c.preempt+512)).Needed → 0<c.coverage.capacity.toNat)
    (read : RandomBuffer c.coverage (c.preempt+512) a) :
    AllowedipsCoverageWrites c.coverage c.preempt a := by
  refine ⟨.inr read.1,?_⟩
  rcases read.2 with header | buffer
  · obtain ⟨i,hi,eq⟩ := header
    have positive := capacity read.1
    exact ⟨i,by omega,eq⟩
  · exact buffer

theorem Core.random_base {n o c initial ra shadow s}
    (core : Core n o c initial ra .outer shadow s) (returnPC target : Int64) :
    (calledState s returnPC target).data.regs.rsp.toBitVec-1024=
      Stack.slot initial.data.regs.rsp.toBitVec 135 := by
  change (s.regs.rsp-8).toBitVec-1024=_
  rw [UInt64.toBitVec_sub]
  change (s.regs.rsp.toBitVec-8)-1024=_
  rw [core.call_slot]
  simp only [Stack.slot,BitVec.sub_sub]
  rfl

theorem ProviderState.push {n o c initial ra config shadow s}
    (facts : ProviderFacts n o c initial ra config)
    (state : ProviderState config c initial ⟨s,0⟩)
    (core : Core n o c initial ra .outer shadow s) (returnPC target : Int64) :
    ProviderState config c initial (calledState s returnPC target) := by
  refine ⟨?_,state.privilege,state.direction,?_⟩
  · have frame := storeInt_frame s.dmem (s.regs.rsp.toBitVec-8) 8 returnPC.toBitVec.toInt
    rw [←RandomProvider.check_frame (before := s.dmem) (after := (calledState s returnPC target).data.dmem) (by
      intro a privateByte
      apply frame a
      rw [core.call_slot]
      intro written
      exact facts.private_external a privateByte (.inl (Stack.scratch _ 7 7 (by decide) (by decide) a written)))]
    exact state.privateCheck
  · intro a width mapped
    exact storeInt_defined _ _ _ _ _ _ (state.mapped a width mapped)

/-- The CALL entry is ready because the current heap satisfies the tested
provider and caller assertions. No service-success premise is used here. -/
theorem Core.random_ready {n o c initial ra config shadow s}
    (facts : FrameFacts n o c initial ra) (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer shadow s)
    (state : ProviderState config c initial ⟨s,0⟩) (returnPC target : Int64) :
    RandomReady config c.coverage (c.preempt+512) (calledState s returnPC target) := by
  let called := calledState s returnPC target
  have providerState := state.push provider core returnPC target
  have memory := core.memory.call_store facts returnPC.toBitVec
  have actualMemory : called.data.dmem=s.dmem.storeInt (Stack.slot initial.data.regs.rsp.toBitVec 7) 8 returnPC.toBitVec.toInt := by
    simp only [called,calledState,core.call_slot]
  have live (a : BitVec 64) (inside : RandomLiveStack called a) : Index.LiveStack initial 135 a := by
    unfold RandomLiveStack at inside
    rw [core.random_base] at inside
    obtain ⟨i,hi,eq⟩ := inside
    exact ⟨i,by omega,eq⟩
  have scratch (a : BitVec 64) (inside : RandomLiveStack called a) : Index.StackBytes initial 135 a := by
    unfold RandomLiveStack at inside
    rw [core.random_base] at inside
    obtain ⟨i,hi,eq⟩ := inside
    exact ⟨i,by omega,eq⟩
  have service (a : BitVec 64)
      (read : RandomMetadata c.coverage (c.preempt+512) a ∨ RandomBuffer c.coverage (c.preempt+512) a) :
      AllowedipsServiceBytes c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a := by
    rcases read with metadata | buffer
    · exact (random_metadata metadata).elim (fun h => .inl (.inl h)) Or.inr
    · exact .inl (.inr ⟨.inr buffer.1,buffer.2⟩)
  refine ⟨?_,?_,provider.capacity,providerState.privateCheck,providerState.privilege,providerState.direction,?_,?_,?_,?_⟩
  · rw [actualMemory]
    simpa only [Index.phase,ite_true,Context.CoverageAt,Context.Needed,
      AllowedipsCoverageAt,AllowedipsCoverageNeeded] using memory.covered true
  · rw [actualMemory]
    exact memory.preempt
  · intro i hi
    rw [core.random_base]
    exact providerState.stack provider i (by omega)
  · intro a privateByte outside
    rcases outside with stack | metadata | buffer
    · exact provider.private_live a privateByte (live a stack)
    · exact provider.private_services a privateByte (service a (.inl metadata))
    · exact provider.private_services a privateByte (service a (.inr buffer))
  · intro a stack outside
    exact provider.wide.geometry.serviceStack a (service a outside) (scratch a stack)
  · intro a buffer metadata
    have written := random_buffer_writes provider.capacity buffer
    rcases random_metadata metadata with field | count
    · exact provider.wide.geometry.bufferMetadata a written field
    · exact provider.wide.geometry.bufferPreempt a written count

#print axioms Core.random_ready
end Binary.Pair.Insert
