import PairIndexCallFacts

namespace Binary.Pair.Trie
open TrustBase CommonBitsCoverage

theorem coverageDataCheck_complete {c : Context} {m : DataMem} (ready : c.CoverageAt m) :
    coverageDataCheck c m=true := by
  unfold coverageDataCheck
  simp only [Bool.and_eq_true,beq_iff_eq]
  refine ⟨⟨⟨ready.1,?_⟩,?_⟩,?_⟩
  · split
    · simpa only [beq_iff_eq] using ready.2.1 ‹_›
    · rfl
  · split
    · simpa only [beq_iff_eq] using ready.2.2.1 ‹_›
    · rfl
  · split
    next needed =>
      obtain ⟨capacity,area,mapped,count,bound,header⟩ := ready.2.2.2 needed
      simp only [Bool.and_eq_true,beq_iff_eq]
      refine ⟨⟨⟨capacity,area⟩,List.all_eq_true.mpr (fun i member => mapped i (List.mem_range.mp member))⟩,?_⟩
      rw [header]
      simp only [BitVec.toNat_ofNat,decide_eq_true_eq]
      exact Nat.le_trans (Nat.mod_le _ _) bound
    next notNeeded => rfl

theorem coverageCheck_complete {c : Context} {m : DataMem} (ready : c.At m) : coverageCheck c m=true := by
  simp only [coverageCheck,Bool.and_eq_true,beq_iff_eq]
  exact ⟨coverageDataCheck_complete ready.1,ready.2⟩
end Binary.Pair.Trie

namespace Binary.Pair.Index
open TrustBase CommonBitsCoverage

theorem CallFacts.checked {n o c s ra words} (facts : CallFacts n o c s ra words) :
    callFrameCheck n o c s ra words=.ok () := by
  apply callFrameCheck_intro
  · simpa only [Bool.and_eq_true,beq_iff_eq,EntryFrame] using facts.entry
  · exact List.all_eq_true.mpr (fun i member => facts.stack i (List.mem_range.mp member))
  · simp only [Bool.and_eq_true]
    exact ⟨Trie.coverageCheck_complete facts.coverage,Trie.coverageDataCheck_complete facts.during⟩
  · simpa only [beq_iff_eq] using facts.hardirq
  · split
    · simpa only [beq_iff_eq] using facts.pending ‹_›
    · rfl
  · exact facts.heapApart
  · exact facts.serviceApart
  · exact facts.bufferApart
  · exact facts.preemptApart

#print axioms CallFacts.checked
end Binary.Pair.Index
