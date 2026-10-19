import SourceAdapter
import PairLookupFacts
import SequentialLookup

namespace Binary.Pair.IndexLookup
open Leanux Leanux.WG TrustBase LookupRelation CommonBitsCoverage Index
set_option maxRecDepth 2048

theorem words_lower (c : Config) : 6≤LookupStackWords c := by
  unfold LookupStackWords
  split <;> decide

theorem outer_live {c : Config} {s : MachineState} {a : BitVec 64}
    (inside : InRange (s.data.regs.rsp.toBitVec-48) 56 a) : LiveStack s (LookupStackWords c) a := by
  have lower := words_lower c
  have run := backwards_range s.data.regs.rsp.toBitVec 48 (8*LookupStackWords c) 8 (by omega) a inside
  exact run

theorem CallFacts.output_heap {n o coverage s w d query kinds ra}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (needed : LookupOutputNeeded (callView (callConfig n w d query kinds) d)) :
    ∀ a, InRange s.data.regs.rcx.toBitVec 8 a → ¬HeapBytes n o a :=
  spansApart_disjoint (facts.outputApart needed) (Covers.range _ _)
    ((show Covers (storageSpans n o) (HeapBytes n o) from fun _ h => h).append_left.append_left)

theorem CallFacts.output_live {n o coverage s w d query kinds ra}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (needed : LookupOutputNeeded (callView (callConfig n w d query kinds) d)) :
    ∀ a, InRange s.data.regs.rcx.toBitVec 8 a → ¬LiveStack s (LookupStackWords (callConfig n w d query kinds)) a :=
  spansApart_disjoint (facts.outputApart needed) (Covers.range _ _)
    ((live_cover _ _).append_right.append_left)

theorem CallFacts.output_services {n o coverage s w d query kinds ra}
    (facts : CallFacts n o coverage s w d query kinds ra)
    (needed : LookupOutputNeeded (callView (callConfig n w d query kinds) d)) :
    ∀ a, InRange s.data.regs.rcx.toBitVec 8 a →
      ¬(AllowedipsServiceBytes coverage.coverage coverage.preempt a ∨ InRange preemptCountAddress 4 a) :=
  spansApart_disjoint (facts.outputApart needed) (Covers.range _ _) (Trie.callServices_cover coverage).append_right

/-- Every M1 entry clause is derived from the tested common relation and
the current call checks. In particular Physical is not a second assumption. -/
theorem CallFacts.entry {n o coverage s w d query kinds ra}
    (facts : CallFacts n o coverage s w d query kinds ra) :
    LookupEntry (callConfig n w d query kinds) coverage.coverage coverage.preempt ra s w
      (callView (callConfig n w d query kinds) d) := by
  let c := callConfig n w d query kinds
  let v := callView c d
  let g := facts.frame.geometry
  have heap := reads_heap (w := w) (query := query) (kinds := kinds) facts.related facts.names
  have dataHeap := data_heap (w := w) (query := query) (kinds := kinds) facts.related facts.names
  have dataCover : Covers (ownerSpans n ++ countSpans n o) (LookupDataWrites c v) := by
    rintro a (owner | ⟨_,count⟩)
    · exact (owner_cover (w := w) (query := query) (kinds := kinds) facts.related facts.names).append_left a owner
    · exact (count_cover (w := w) (query := query) (kinds := kinds) facts.related).append_right a count
  have dataBucket := spansApart_disjoint facts.shapeApart dataCover (bucket_cover (w := w) (query := query) (kinds := kinds) facts.related facts.names)
  have ownerCount := spansApart_disjoint facts.countApart (owner_cover (w := w) (query := query) (kinds := kinds) facts.related facts.names) (count_cover (w := w) (query := query) (kinds := kinds) facts.related)
  have returnLive : ∀ a, InRange s.data.regs.rsp.toBitVec 8 a → LiveStack s (LookupStackWords c) a := by
    intro a inside
    exact Stack.inside _ _ 0 (by omega) a (by simpa only [Stack.slot,Nat.mul_zero,BitVec.sub_zero] using inside)
  refine ⟨facts.pc,facts.frame.entry,facts.table,facts.queryAt,facts.kindsAt,?_,call_focus facts.related,
    call_physical facts.related facts.storage facts.names,rfl,rfl,
    coverage_of_phases facts.frame.coverage.1 facts.frame.during,facts.frame.coverage.2,
    facts.frame.stack,facts.outputMapped,?_,facts.frame.pending,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold project
    rw [facts.device]
    rfl
  · simpa only [BitVec.add_comm] using facts.frame.hardirq
  · intro a read written
    rcases written with stack | buffer | preempt
    · exact g.heap_external a (heap a read) (.inl stack)
    · exact g.heap_external a (heap a read) (.inr (.inl (coverage_writes buffer)))
    · exact g.heap_external a (heap a read) (.inr (.inr preempt))
  · intro a service stack
    exact g.serviceStack a (coverage_services service) stack
  · intro a buffer stack
    exact g.bufferLive a (coverage_writes buffer) stack
  · intro a buffer metadata
    exact g.bufferMetadata a (coverage_writes buffer) (coverage_metadata metadata)
  · intro a buffer preempt
    exact g.bufferPreempt a (coverage_writes buffer) preempt
  · intro a preempt stack
    exact g.preemptLive a stack preempt
  · rintro a (metadata | ⟨needed,storage⟩) preempt
    · exact g.preemptMetadata a (coverage_metadata metadata) preempt
    · rcases storage with header | buffer
      · exact g.preemptHeader a (needed_phases needed) header preempt
      · exact g.bufferPreempt a ⟨needed_phases needed,buffer⟩ preempt
  · intro a service data
    exact g.heapService a (dataHeap a data) (coverage_services service)
  · intro a ret data
    exact g.heapLive a (dataHeap a data) (returnLive a ret)
  · intro a bucket data
    exact dataBucket a data bucket
  · intro a count owner
    exact ownerCount a owner count
  · rintro a ⟨needed,output⟩ (read | service | stack | buffer)
    · exact facts.output_heap needed a output (heap a read)
    · exact facts.output_services needed a output (coverage_services service)
    · exact facts.output_live needed a output (outer_live stack)
    · exact facts.output_services needed a output (.inl (.inr ⟨needed_phases buffer.1,.inr buffer.2⟩))
  · intro needed a pending written
    have metadata : AllowedipsMetadata coverage.coverage coverage.preempt a :=
      .inr (.inr (.inr (.inr ⟨needed,pending⟩)))
    rcases written with stack | buffer | data | ⟨outputNeeded,output⟩
    · exact g.serviceStack a (.inl (.inl metadata)) stack
    · exact g.bufferMetadata a (coverage_writes buffer) metadata
    · exact g.heapService a (dataHeap a data) (.inl (.inl metadata))
    · exact facts.output_services outputNeeded a output (.inl (.inl metadata))

theorem pre_lookup {n o coverage s w query kinds ra} (checked : Pre n o coverage s w query kinds ra) :
    ∃ d, w.wg.dev=some d ∧ Pre_lookup (callConfig n w d query kinds) coverage.coverage coverage.preempt ra s w := by
  obtain ⟨d,facts⟩ := pre_facts checked
  exact ⟨d,facts.device,_,facts.entry⟩

#print axioms pre_lookup
end Binary.Pair.IndexLookup
