import PairReplaceState

namespace Binary.Pair.Replace
open TrustBase CommonBitsCoverage Index

/-- Each physical heap store advances the same shadow memory. The source
reconstruction is required only at the segment endpoint. -/
theorem Core.store {n o c initial ra disabled shadow result s}
    (facts : CallFacts n o c initial ra 5) (core : Core c initial ra disabled shadow result s)
    (address : BitVec 64) (width : Nat) (value : Int)
    (heap : ∀ a, InRange address width a → HeapBytes n o a) :
    Core c initial ra disabled (shadow.storeInt address width value) result
      {s with dmem := s.dmem.storeInt address width value} := by
  exact ⟨core.stack,core.owner,core.new,core.r13,core.r14,core.r15,
    core.memory.frame facts.geometry (storeInt_frame _ _ _ _) heap,
    core.frame.storeInt _ _ _⟩

theorem Core.load {n o c initial ra disabled shadow result s address width}
    (facts : CallFacts n o c initial ra 5) (core : Core c initial ra disabled shadow result s)
    (heap : ∀ a, InRange address width a → HeapBytes n o a) :
    s.dmem.loadInt address width=shadow.loadInt address width :=
  (external_read facts.geometry core.frame heap).symm

#print axioms Core.store
end Binary.Pair.Replace
