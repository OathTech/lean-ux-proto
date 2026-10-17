import PairLoopCheck
import AllowedipsLoopFrame

namespace Binary.Pair.Trie
open TrustBase CommonBitsCoverage

theorem metadataSpans_cover {c : Context} {a : BitVec 64} (read : c.metadataBytes a) :
    ∃ span ∈ metadataSpans c, span.contains a := by
  rcases read with current | ⟨soft,read⟩ | ⟨mode,read⟩ | ⟨needed,read | read⟩
  · exact ⟨(currentTaskAddress.toNat,8),by simp [metadataSpans],by simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using current⟩
  · exact ⟨((c.coverage.task+0x704).toNat,4),by simp [metadataSpans,soft],by simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using read⟩
  · exact ⟨((c.coverage.task+0x6e0).toNat,4),by simp [metadataSpans,mode],by simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using read⟩
  · exact ⟨((c.coverage.task+0x6e4).toNat,4),by simp [metadataSpans,needed],by simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using read⟩
  · exact ⟨((c.coverage.task+0x6e8).toNat,8),by simp [metadataSpans,needed],by simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using read⟩

theorem writeSpans_cover {c : Context} {a : BitVec 64} (write : c.writes a) :
    ∃ span ∈ writeSpans c, span.contains a :=
  ⟨(c.coverage.area.toNat,8*c.coverage.capacity.toNat),by simp [writeSpans,write.1],by simpa [Span.contains,KcovBufferBytes] using write.2⟩

theorem readSpans_cover {c : Context} {a : BitVec 64} (read : c.bytes a) :
    ∃ span ∈ readSpans c, span.contains a := by
  rcases read with metadata | preempt | ⟨needed,header | buffer⟩
  · obtain ⟨span,member,inside⟩ := metadataSpans_cover metadata
    exact ⟨span,by simp [readSpans,member],inside⟩
  · exact ⟨(preemptCountAddress.toNat,4),by simp [readSpans],by simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using preempt⟩
  · exact ⟨(c.coverage.area.toNat,8),by simp [readSpans,needed],by simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using header⟩
  · obtain ⟨span,member,inside⟩ := writeSpans_cover ⟨needed,buffer⟩
    exact ⟨span,by simp [readSpans,needed,member],inside⟩

theorem coverageCheck_sound {c : Context} {m : DataMem} (ok : coverageCheck c m = true) : c.At m := by
  simp only [coverageCheck,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨task,preempt⟩,soft⟩,mode⟩,buffer⟩ := ok
  refine ⟨⟨task,?_,?_,?_⟩,preempt⟩
  · intro read
    simpa only [read,↓reduceIte,beq_iff_eq] using soft
  · intro read
    simpa only [read,↓reduceIte,beq_iff_eq] using mode
  · intro needed
    simp only [needed,↓reduceIte,Bool.and_eq_true,beq_iff_eq] at buffer
    obtain ⟨⟨⟨capacity,area⟩,mapped⟩,header⟩ := buffer
    refine ⟨capacity,area,?_,?_⟩
    · intro word bound
      exact List.all_eq_true.mp mapped word (List.mem_range.mpr bound)
    · cases read : load64 m c.coverage.area with
      | none => rw [read] at header; cases header
      | some count =>
        refine ⟨count.toNat,?_,?_⟩
        · simpa only [read,decide_eq_true_eq] using header
        · simp

/-- The tested service-data assertion establishes all physical frame
premises. Callback behavior remains a separately named semantic contract. -/
theorem frameCheck_sound {c : Context} {s : MachineData} (ok : frameCheck c s = true) :
    AllowedipsLoop.Frame s c s := by
  simp only [frameCheck,Bool.and_eq_true,beq_iff_eq] at ok
  obtain ⟨⟨⟨⟨coverage,aligned⟩,mapped⟩,separation⟩,metadata⟩ := ok
  have slots : ∀ n < 6, (s.dmem.loadInt (s.regs.rsp.toBitVec-.ofNat 64 ((n+1)*8)) 8).isSome = true :=
    fun n hn => List.all_eq_true.mp mapped n (List.mem_range.mpr hn)
  have outside : ∀ a, c.bytes a → ¬InRange (s.regs.rsp.toBitVec-48) 48 a := by
    intro a read inside
    obtain ⟨span,member,atSpan⟩ := readSpans_cover read
    apply spansApart_sound separation (r := ((s.regs.rsp.toBitVec-48).toNat,48)) member (by simp) atSpan
    simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using inside
  have wordOutside : ∀ a, c.bytes a → ¬InRange (s.regs.rsp.toBitVec-8) 8 a := by
    intro a read inside
    apply outside a read
    exact AllowedipsLoop.stack_slot_inside s.regs.rsp 0 (by decide) a inside
  have metadataApart : ∀ a, c.writes a → ¬c.metadataBytes a := by
    intro a write read
    obtain ⟨l,hl,inside⟩ := writeSpans_cover write
    obtain ⟨r,hr,atRight⟩ := metadataSpans_cover read
    exact spansApart_sound metadata hl (List.mem_append_left _ hr) inside atRight
  have preemptApart : ∀ a, c.writes a → ¬InRange preemptCountAddress 4 a := by
    intro a write read
    obtain ⟨l,hl,inside⟩ := writeSpans_cover write
    apply spansApart_sound metadata (r := (preemptCountAddress.toNat,4)) hl (by simp) inside
    simpa only [Span.contains,BitVec.ofNat_toNat,BitVec.setWidth_eq] using read
  apply AllowedipsLoop.Frame.initial s c
  · exact ⟨coverageCheck_sound coverage,aligned,slots 0 (by decide),wordOutside,
      fun a write => wordOutside a (.inr (.inr ⟨write.1,.inr write.2⟩)),metadataApart,preemptApart⟩
  · exact slots
  · exact outside

#print axioms frameCheck_sound
end Binary.Pair.Trie
