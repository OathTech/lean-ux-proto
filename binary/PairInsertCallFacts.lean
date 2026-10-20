import PairInsert
import PairRemovePre
import PairInsertCoverage

namespace Binary.Pair.Insert
open Leanux Leanux.WG TrustBase CommonBitsCoverage

/-- Present-state resources of all three BH phases. These clauses are derived
from the executable entry assertion; none describes a future execution. -/
structure FrameFacts (n : Names) (o : Offsets) (c : Context)
    (s : MachineState) (ra : UInt64) : Prop extends Index.CallFacts n o c s ra 7 where
  nested : (Context.mk c.coverage (c.preempt+1024)).CoverageAt s.data.dmem
  nestedHardirq : (c.preempt+1024) &&& 0x000f0000=0
  nestedPending : LookupPendingRead (c.preempt+512) →
    s.data.dmem.loadInt softirqPendingAddress 2=some 0
  nestedApart : LookupPendingRead (c.preempt+512) →
    spansApart [(softirqPendingAddress.toNat,2)]
      (Index.storageSpans n o ++ Index.callStack s 7 false ++ Trie.callBuffers c ++
        [(preemptCountAddress.toNat,4)])=true

theorem boundary_frame {n o c s w owner ra}
    (checked : callBoundary n o c s w owner ra=.ok ()) : FrameFacts n o c s ra := by
  unfold callBoundary at checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,_,checked⟩ := bind_ok checked
  obtain ⟨_,frame,checked⟩ := bind_ok checked
  obtain ⟨coverage,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨hardirq,checked⟩ := check_ok _ _ _ _ checked
  have frame : Index.callFrameCheck n o c s ra 7=.ok () := by
    cases frameResult : Index.callFrameCheck n o c s ra 7 with
    | error e => rw [frameResult] at frame; cases frame
    | ok u => cases u; rfl
  refine ⟨Index.callFrameCheck_sound frame,Trie.coverageDataCheck_sound coverage,eq_of_beq hardirq,?_,?_⟩
  all_goals
    intro needed
    simp only [needed,↓reduceIte] at checked
    obtain ⟨pending,checked⟩ := check_ok _ _ _ _ checked
    obtain ⟨apart,_⟩ := check_ok _ _ _ _ checked
  · exact eq_of_beq pending
  · exact apart

/-- The extra pending word is separate exactly when the nested enable reads
it. This does not require the original preempt count to avoid wraparound. -/
theorem FrameFacts.pending_disjoint {n o c s ra} (facts : FrameFacts n o c s ra)
    (needed : LookupPendingRead (c.preempt+512)) :
    ∀ a, InRange softirqPendingAddress 2 a →
      ¬(Index.HeapBytes n o a ∨ Index.StackBytes s 7 a ∨
        AllowedipsCoverageWrites c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a) := by
  intro a inside written
  have apart := facts.nestedApart needed
  have pending := Covers.range softirqPendingAddress 2
  have heap : Covers (Index.storageSpans n o) (Index.HeapBytes n o) := fun _ h => h
  rcases written with heapWritten | stackWritten | bufferWritten | countWritten
  · exact spansApart_disjoint apart pending heap.append_left.append_left.append_left a inside heapWritten
  · exact spansApart_disjoint apart pending (Index.stack_cover s 7).append_right.append_left.append_left a inside stackWritten
  · exact spansApart_disjoint apart pending (Trie.callBuffers_cover c).append_right.append_left a inside bufferWritten
  · exact spansApart_disjoint apart pending (Covers.range preemptCountAddress 4).append_right a inside countWritten

#print axioms boundary_frame
#print axioms FrameFacts.pending_disjoint
end Binary.Pair.Insert
