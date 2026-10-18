import PairIndexCallFacts
import PairStack
import AllowedipsCoverage

namespace Binary.Pair.Index
open TrustBase CommonBitsCoverage

def HeapBytes (n : Names) (o : Offsets) (a : BitVec 64) : Prop :=
  ∃ span ∈ storageSpans n o, span.contains a
def StackBytes (s : MachineState) (words : Nat) : BitVec 64 → Prop :=
  InRange (Stack.slot s.data.regs.rsp.toBitVec words) (8*words)
def LiveStack (s : MachineState) (words : Nat) : BitVec 64 → Prop :=
  InRange (Stack.slot s.data.regs.rsp.toBitVec words) (8*words+8)

theorem stack_cover (s : MachineState) (words : Nat) : Covers (callStack s words false) (StackBytes s words) := by
  simpa [callStack,StackBytes,Stack.slot] using Covers.range (Stack.slot s.data.regs.rsp.toBitVec words) (8*words)
theorem live_cover (s : MachineState) (words : Nat) : Covers (callStack s words true) (LiveStack s words) := by
  simpa [callStack,LiveStack,Stack.slot] using Covers.range (Stack.slot s.data.regs.rsp.toBitVec words) (8*words+8)

structure Geometry (n : Names) (o : Offsets) (c : Context) (s : MachineState) (words : Nat) : Prop where
  heapLive : ∀ a, HeapBytes n o a → ¬LiveStack s words a
  heapService : ∀ a, HeapBytes n o a → ¬(AllowedipsServiceBytes c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a)
  serviceStack : ∀ a, AllowedipsServiceBytes c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a → ¬StackBytes s words a
  bufferLive : ∀ a, AllowedipsCoverageWrites c.coverage c.preempt a → ¬LiveStack s words a
  bufferMetadata : ∀ a, AllowedipsCoverageWrites c.coverage c.preempt a → ¬AllowedipsMetadata c.coverage c.preempt a
  bufferPreempt : ∀ a, AllowedipsCoverageWrites c.coverage c.preempt a → ¬InRange preemptCountAddress 4 a
  preemptLive : ∀ a, LiveStack s words a → ¬InRange preemptCountAddress 4 a
  preemptMetadata : ∀ a, AllowedipsMetadata c.coverage c.preempt a → ¬InRange preemptCountAddress 4 a
  preemptHeader : ∀ a, (c.Needed ∨ (Context.mk c.coverage (c.preempt+512)).Needed) →
    InRange c.coverage.area 8 a → ¬InRange preemptCountAddress 4 a

theorem CallFacts.geometry {n o c s ra words} (facts : CallFacts n o c s ra words) : Geometry n o c s words := by
  have heap : Covers (storageSpans n o) (HeapBytes n o) := fun _ h => h
  have preempt := Covers.range preemptCountAddress 4
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact spansApart_disjoint facts.heapApart heap (live_cover s words).append_left
  · exact spansApart_disjoint facts.heapApart heap (Trie.callServices_cover c).append_right
  · exact spansApart_disjoint facts.serviceApart (Trie.callServices_cover c) (stack_cover s words)
  · exact spansApart_disjoint facts.bufferApart (Trie.callBuffers_cover c) (live_cover s words).append_left.append_left
  · exact spansApart_disjoint facts.bufferApart (Trie.callBuffers_cover c) (Trie.callMetadata_cover c).append_right.append_left
  · exact spansApart_disjoint facts.bufferApart (Trie.callBuffers_cover c) preempt.append_right
  · exact spansApart_disjoint facts.preemptApart (live_cover s words).append_left.append_left preempt
  · exact spansApart_disjoint facts.preemptApart (Trie.callMetadata_cover c).append_right.append_left preempt
  · intro a needed inside
    have member : (c.coverage.area.toNat,8) ∈ Trie.callHeaders c := by
      unfold Trie.callHeaders
      rw [ite_eq_left needed]
      simp
    have apart := spansApart_sound (a := a) facts.preemptApart
      (List.mem_append_right _ member) (List.mem_singleton_self (preemptCountAddress.toNat,4))
    apply (show InRange c.coverage.area 8 a → ¬InRange preemptCountAddress 4 a from by
      simpa [Span.contains] using apart)
    exact inside

theorem stack_live {s words a} (inside : StackBytes s words a) : LiveStack s words a := by
  obtain ⟨i,hi,eq⟩ := inside
  exact ⟨i,by omega,eq⟩

theorem Geometry.heap_before {n o c s words} (g : Geometry n o c s words) :
    ∀ a, HeapBytes n o a → ¬c.bytes a := by
  intro a heap service
  exact g.heapService a heap (AllowedipsCoverage.bytes_before c.coverage c.preempt a service)
theorem Geometry.heap_during {n o c s words} (g : Geometry n o c s words) :
    ∀ a, HeapBytes n o a → ¬(Context.mk c.coverage (c.preempt+512)).bytes a := by
  intro a heap service
  exact g.heapService a heap (AllowedipsCoverage.bytes_during c.coverage c.preempt a service)

#print axioms CallFacts.geometry
end Binary.Pair.Index
