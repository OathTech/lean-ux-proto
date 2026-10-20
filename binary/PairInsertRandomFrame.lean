import PairInsertRandomReady

namespace Binary.Pair.Insert
open TrustBase CommonBitsCoverage Instrumentation

theorem Core.random_slot {n o c initial ra config shadow s}
    (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer shadow s) (returnPC target : Int64)
    (i : Nat) (bound : i≤7) :
    ∀ a, RandomWrites config c.coverage (c.preempt+512) (calledState s returnPC target) a →
      ¬InRange (Stack.slot initial.data.regs.rsp.toBitVec i) 8 a := by
  intro a written slot
  have live := Stack.inside initial.data.regs.rsp.toBitVec 135 i (by omega) a slot
  rcases written with privateByte | stack | buffer
  · exact provider.private_live a privateByte live
  · unfold RandomStack at stack
    rw [core.random_base] at stack
    rw [Stack.window initial.data.regs.rsp.toBitVec 135 i (by omega)] at slot
    have apart := InRange.offset_disjoint (Stack.slot initial.data.regs.rsp.toBitVec 135)
      0 1024 (8*(135-i)) 8 (by decide) (by omega) (by omega) a
    apply apart _ slot
    simpa only [BitVec.add_zero] using stack
  · exact provider.wide.geometry.bufferLive a ⟨.inr buffer.1,buffer.2⟩ live

theorem Core.random_heap {n o c initial ra config shadow s}
    (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer shadow s) (returnPC target : Int64) :
    ∀ a, Index.HeapBytes n o a →
      ¬RandomWrites config c.coverage (c.preempt+512) (calledState s returnPC target) a := by
  intro a heap written
  rcases written with privateByte | stack | buffer
  · exact provider.private_heap a privateByte heap
  · unfold RandomStack at stack
    rw [core.random_base] at stack
    obtain ⟨i,hi,eq⟩ := stack
    exact provider.wide.geometry.heapLive a heap ⟨i,by omega,eq⟩
  · exact provider.wide.geometry.heapService a heap (.inl (.inr ⟨.inr buffer.1,.inr buffer.2⟩))

theorem Core.random_storage {n o c initial ra config shadow s after}
    (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer shadow s) (returnPC target : Int64)
    (frame : EqualOutside (RandomWrites config c.coverage (c.preempt+512) (calledState s returnPC target))
      (calledState s returnPC target).data.dmem after) :
    Index.StorageFrame n o (calledState s returnPC target).data.dmem after := by
  apply Index.StorageFrame.of_execution frame
  intro span member a inside
  exact core.random_heap provider returnPC target a ⟨span,member,inside⟩

theorem Core.random_metadata_apart {n o c initial ra config shadow s}
    (provider : ProviderFacts n o c initial ra config)
    (core : Core n o c initial ra .outer shadow s) (returnPC target : Int64) (b : Bool) :
    ∀ a, (Index.phase c b).metadataBytes a →
      ¬RandomWrites config c.coverage (c.preempt+512) (calledState s returnPC target) a := by
  intro a metadata written
  have metadata : AllowedipsMetadata c.coverage c.preempt a := by
    cases b with
    | false => exact AllowedipsCoverage.metadata_before _ _ _ metadata
    | true => exact AllowedipsCoverage.metadata_during _ _ _ metadata
  rcases written with privateByte | stack | buffer
  · exact provider.private_services a privateByte (.inl (.inl metadata))
  · unfold RandomStack at stack
    rw [core.random_base] at stack
    obtain ⟨i,hi,eq⟩ := stack
    exact provider.wide.geometry.serviceStack a (.inl (.inl metadata)) ⟨i,by omega,eq⟩
  · exact provider.wide.geometry.bufferMetadata a ⟨.inr buffer.1,buffer.2⟩ metadata

#print axioms Core.random_storage
#print axioms Core.random_slot
#print axioms Core.random_metadata_apart
end Binary.Pair.Insert
