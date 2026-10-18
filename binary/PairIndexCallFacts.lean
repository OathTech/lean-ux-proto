import PairIndexCallCheck
import PairCallFacts

namespace Binary.Pair.Index
open TrustBase CommonBitsCoverage
set_option maxRecDepth 2048

structure CallFacts (n : Names) (o : Offsets) (c : Context)
    (s : MachineState) (ra : UInt64) (words : Nat) : Prop where
  entry : EntryFrame s ra
  stack : ∀ i < words, (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec-.ofNat 64 ((i+1)*8)) 8).isSome=true
  coverage : c.At s.data.dmem
  during : AllowedipsCoverageAt c.coverage (c.preempt+512) s.data.dmem
  hardirq : (c.preempt+512) &&& 0x000f0000=0
  pending : LookupPendingRead c.preempt → s.data.dmem.loadInt softirqPendingAddress 2=some 0
  heapApart : spansApart (storageSpans n o) (callStack s words true ++ Trie.callServices c)=true
  serviceApart : spansApart (Trie.callServices c) (callStack s words false)=true
  bufferApart : spansApart (Trie.callBuffers c)
    (callStack s words true ++ Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)])=true
  preemptApart : spansApart (callStack s words true ++ Trie.callMetadata c ++ Trie.callHeaders c)
    [(preemptCountAddress.toNat,4)]=true

theorem callFrameCheck_sound {n o c s ra words}
    (checked : callFrameCheck n o c s ra words=.ok ()) : CallFacts n o c s ra words := by
  unfold callFrameCheck at checked
  obtain ⟨entry,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨stack,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨coverage,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨hardirq,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨pending,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨heap,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨services,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨buffers,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨preempt,_⟩ := check_ok _ _ _ _ checked
  have phases : Trie.coverageCheck c s.data.dmem=true ∧
      Trie.coverageDataCheck ⟨c.coverage,c.preempt+512⟩ s.data.dmem=true := by
    simpa only [Bool.and_eq_true] using coverage
  refine ⟨by simpa [EntryFrame] using entry,
    fun i hi => List.all_eq_true.mp stack i (List.mem_range.mpr hi),
    Trie.coverageCheck_sound phases.1,Trie.coverageDataCheck_sound phases.2,
    eq_of_beq hardirq,?_,heap,services,buffers,preempt⟩
  intro needed
  simpa only [needed,↓reduceIte,beq_iff_eq] using pending

#print axioms callFrameCheck_sound

/-- Build the unchanged executable check one guard at a time. Keeping its
continuation abstract avoids expanding every failing branch in witnesses. -/
theorem callFrameCheck_intro {n o c s ra words}
    (entry : (s.data.regs.rsp.toNat%8==0 && s.data.dmem.loadInt s.data.regs.rsp.toBitVec 8==some (ra.toNat : Int))=true)
    (stack : (List.range words).all (fun i => (s.data.dmem.loadInt
      (s.data.regs.rsp.toBitVec-.ofNat 64 ((i+1)*8)) 8).isSome)=true)
    (coverage : (Trie.coverageCheck c s.data.dmem &&
      Trie.coverageDataCheck ⟨c.coverage,c.preempt+512⟩ s.data.dmem)=true)
    (hardirq : ((c.preempt+512) &&& 0x000f0000==0)=true)
    (pending : (if LookupPendingRead c.preempt then s.data.dmem.loadInt softirqPendingAddress 2==some 0 else true)=true)
    (heap : spansApart (storageSpans n o) (callStack s words true ++ Trie.callServices c)=true)
    (services : spansApart (Trie.callServices c) (callStack s words false)=true)
    (buffers : spansApart (Trie.callBuffers c)
      (callStack s words true ++ Trie.callMetadata c ++ [(preemptCountAddress.toNat,4)])=true)
    (preempt : spansApart (callStack s words true ++ Trie.callMetadata c ++ Trie.callHeaders c)
      [(preemptCountAddress.toNat,4)]=true) : callFrameCheck n o c s ra words=.ok () := by
  unfold callFrameCheck
  apply check_of _ _ _ _ entry
  apply check_of _ _ _ _ stack
  apply check_of _ _ _ _ coverage
  apply check_of _ _ _ _ hardirq
  apply check_of _ _ _ _ pending
  apply check_of _ _ _ _ heap
  apply check_of _ _ _ _ services
  apply check_of _ _ _ _ buffers
  apply check_of _ _ _ _ preempt
  rfl
end Binary.Pair.Index
