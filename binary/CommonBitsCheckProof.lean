import CommonBitsCheck
import PairFrameProof

namespace Binary.Pair.Common
open CommonBits

theorem callerCheck_sound {i c s returnPC} (checked : callerCheck i c s returnPC=true) :
    CallerAt i c s returnPC := by
  simp only [callerCheck,Bool.and_eq_true,beq_iff_eq] at checked
  obtain ⟨⟨⟨frame,fields⟩,words⟩,separation⟩ := checked
  have physical := Trie.frameCheck_sound frame
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨node,key⟩,stack⟩,family⟩,bx⟩,bp⟩,r12⟩,r13⟩,address⟩ := fields
  refine ⟨node,key,stack,family,bx,bp,r12,r13,address,?_,?_,physical.ready.state,
    physical.ready.aligned,physical.mapped,physical.coverageSeparate,
    physical.ready.metadataSeparate,physical.ready.preemptSeparate⟩
  · intro word member
    exact beq_iff_eq.mp (List.all_eq_true.mp words word member)
  · rintro a ⟨word,member,inside⟩ (scratch | coverage)
    · apply spansApart_sound separation
        (List.mem_map.mpr ⟨word,member,rfl⟩) (r := ((s.regs.rsp.toBitVec-48).toNat,48)) (by simp)
      · simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using inside
      · simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq,CallerScratch] using scratch
    · obtain ⟨span,spanMember,atSpan⟩ := Trie.writeSpans_cover coverage
      apply spansApart_sound separation (List.mem_map.mpr ⟨word,member,rfl⟩)
        (List.mem_append_right _ spanMember) _ atSpan
      simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using inside

#print axioms callerCheck_sound
end Binary.Pair.Common
