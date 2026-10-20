import PairCallCheck
import PairFrameProof
import CanonicalLoads

namespace Binary.Pair.Trie
open TrustBase CommonBitsCoverage
set_option maxRecDepth 2048

theorem load64_raw (m : DataMem) (base : BitVec 64) (word : BitVec 64)
    (read : load64 m base = some word) : m.loadInt base 8 = some (word.toNat : Int) := by
  cases raw : m.loadInt base 8 with
  | none => simp [load64,raw] at read
  | some n =>
    have equal : word = BitVec.ofInt 64 n := by simpa [load64,raw] using read.symm
    obtain ⟨nonnegative,bound⟩ := loadInt_range m base 8 n raw
    rw [equal]
    congr 1
    simp only [BitVec.toNat_ofInt]
    rw [Int.emod_eq_of_lt nonnegative (by simpa using bound), Int.toNat_of_nonneg nonnegative]

theorem networkKeyCheck_sound {m : DataMem} {base : BitVec 64} {bits key : Nat}
    (checked : networkKeyCheck m base bits key = true) : Allowedips.NetworkKey m base bits key := by
  unfold networkKeyCheck at checked
  unfold Allowedips.NetworkKey
  by_cases family : bits = 32
  · simp only [family,beq_self_eq_true,↓reduceIte] at checked ⊢
    cases read : load32 m base with
    | none => rw [read] at checked; cases checked
    | some word =>
      rw [read] at checked
      exact ⟨word,load32_raw _ _ _ read,eq_of_beq checked⟩
  · simp only [beq_iff_eq,family,↓reduceIte] at checked ⊢
    cases hi : load64 m base with
    | none => rw [hi] at checked; cases checked
    | some high =>
      cases lo : load64 m (base+8) with
      | none => rw [hi,lo] at checked; cases checked
      | some low =>
        rw [hi,lo] at checked
        exact ⟨high,low,load64_raw _ _ _ hi,
          load64_raw _ _ _ lo,eq_of_beq checked⟩

theorem callMetadata_cover (c : Context) : Covers (callMetadata c) (AllowedipsMetadata c.coverage c.preempt) := by
  intro a read
  rcases read with current | ⟨soft,read⟩ | ⟨mode,read⟩ | ⟨needed,read⟩ | ⟨pending,read⟩
  · obtain ⟨span,member,inside⟩ := metadataSpans_cover (c := c) (.inl current)
    exact ⟨span,List.mem_append_left _ (List.mem_append_left _ member),inside⟩
  · rcases soft with before | during
    · obtain ⟨span,member,inside⟩ := metadataSpans_cover (c := c) (.inr (.inl ⟨before,read⟩))
      exact ⟨span,List.mem_append_left _ (List.mem_append_left _ member),inside⟩
    · obtain ⟨span,member,inside⟩ := metadataSpans_cover (c := ⟨c.coverage,c.preempt+512⟩) (.inr (.inl ⟨during,read⟩))
      exact ⟨span,List.mem_append_left _ (List.mem_append_right _ member),inside⟩
  · rcases mode with before | during
    · obtain ⟨span,member,inside⟩ := metadataSpans_cover (c := c) (.inr (.inr (.inl ⟨before,read⟩)))
      exact ⟨span,List.mem_append_left _ (List.mem_append_left _ member),inside⟩
    · obtain ⟨span,member,inside⟩ := metadataSpans_cover (c := ⟨c.coverage,c.preempt+512⟩) (.inr (.inr (.inl ⟨during,read⟩)))
      exact ⟨span,List.mem_append_left _ (List.mem_append_right _ member),inside⟩
  · rcases needed with before | during
    · obtain ⟨span,member,inside⟩ := metadataSpans_cover (c := c) (.inr (.inr (.inr ⟨before,read⟩)))
      exact ⟨span,List.mem_append_left _ (List.mem_append_left _ member),inside⟩
    · obtain ⟨span,member,inside⟩ := metadataSpans_cover (c := ⟨c.coverage,c.preempt+512⟩) (.inr (.inr (.inr ⟨during,read⟩)))
      exact ⟨span,List.mem_append_left _ (List.mem_append_right _ member),inside⟩
  · exact ⟨(softirqPendingAddress.toNat,2),by simp [callMetadata,pending],by simpa [Span.contains] using read⟩

theorem callBuffers_cover (c : Context) : Covers (callBuffers c) (AllowedipsCoverageWrites c.coverage c.preempt) := by
  intro a read
  rcases read with ⟨before | during,buffer⟩
  · obtain ⟨span,member,inside⟩ := writeSpans_cover (c := c) ⟨before,buffer⟩
    exact ⟨span,List.mem_append_left _ member,inside⟩
  · obtain ⟨span,member,inside⟩ := writeSpans_cover (c := ⟨c.coverage,c.preempt+512⟩) ⟨during,buffer⟩
    exact ⟨span,List.mem_append_right _ member,inside⟩

theorem callServices_cover (c : Context) : Covers (callServices c)
    (fun a => AllowedipsServiceBytes c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a) := by
  intro a read
  have before (read : c.bytes a) : ∃ span ∈ callServices c, span.contains a := by
    obtain ⟨span,member,inside⟩ := readSpans_cover read
    exact ⟨span,List.mem_append_left _ (List.mem_append_left _ member),inside⟩
  have during (read : (Context.mk c.coverage (c.preempt+512)).bytes a) :
      ∃ span ∈ callServices c, span.contains a := by
    obtain ⟨span,member,inside⟩ := readSpans_cover read
    exact ⟨span,List.mem_append_left _ (List.mem_append_right _ member),inside⟩
  rcases read with (metadata | ⟨needed,buffer⟩) | preempt
  · rcases metadata with current | ⟨soft,read⟩ | ⟨mode,read⟩ | ⟨needed,read⟩ | ⟨pending,read⟩
    · exact before (.inl (.inl current))
    · rcases soft with h | h
      · exact before (.inl (.inr (.inl ⟨h,read⟩)))
      · exact during (.inl (.inr (.inl ⟨h,read⟩)))
    · rcases mode with h | h
      · exact before (.inl (.inr (.inr (.inl ⟨h,read⟩))))
      · exact during (.inl (.inr (.inr (.inl ⟨h,read⟩))))
    · rcases needed with h | h
      · exact before (.inl (.inr (.inr (.inr ⟨h,read⟩))))
      · exact during (.inl (.inr (.inr (.inr ⟨h,read⟩))))
    · exact ⟨(softirqPendingAddress.toNat,2),by simp [callServices,pending],by simpa [Span.contains] using read⟩
  · rcases needed with h | h
    · exact before (.inr (.inr ⟨h,buffer⟩))
    · exact during (.inr (.inr ⟨h,buffer⟩))
  · exact before (.inr (.inl preempt))

def CountBytes (names : Names) (o : AllowedipsProbe.Offsets) (a : BitVec 64) : Prop :=
  ∃ id base, (id,base) ∈ names.peers ∧ InRange (.ofNat 64 (base+o.peerRefcount)) 4 a

theorem countSpans_cover (names : Names) (o : AllowedipsProbe.Offsets) :
    Covers (countSpans names o) (CountBytes names o) := by
  rintro a ⟨id,base,member,inside⟩
  exact ⟨(base+o.peerRefcount,4),List.mem_map.mpr ⟨(id,base),member,rfl⟩,inside⟩

theorem trieSpans_cover (names : Names) (o : AllowedipsProbe.Offsets) :
    Covers (trieSpans names o) (NodeReadBytes names o) := by
  rintro a ⟨id,base,named,offset,size,field,inside⟩
  exact ⟨(base+offset,size),List.mem_flatMap.mpr
    ⟨(id,base),named,List.mem_map.mpr ⟨(offset,size),field,rfl⟩⟩,inside⟩

structure CallFacts (names : Names) (o : AllowedipsProbe.Offsets) (c : Context)
    (s : MachineState) (ra : UInt64) (bits key : Nat) : Prop where
  entry : EntryFrame s ra
  stack : ∀ i < 18, (s.data.dmem.loadInt (s.data.regs.rsp.toBitVec-.ofNat 64 ((i+1)*8)) 8).isSome = true
  input : Allowedips.NetworkKey s.data.dmem s.data.regs.rdx.toBitVec bits key
  coverage : c.At s.data.dmem
  during : AllowedipsCoverageAt c.coverage (c.preempt+512) s.data.dmem
  hardirq : (c.preempt+512) &&& 0x000f0000 = 0
  pending : LookupPendingRead c.preempt → s.data.dmem.loadInt softirqPendingAddress 2 = some 0
  decoderApart : spansApart (decoderSpans names o)
    (callStack s false ++ callBuffers c ++ [(preemptCountAddress.toNat,4)]) = true
  queryApart : spansApart [(s.data.regs.rdx.toNat,if bits == 32 then 4 else 16)]
    (callStack s false ++ writeSpans c) = true
  serviceApart : spansApart (callServices c) (callStack s false) = true
  bufferApart : spansApart (callBuffers c)
    (callStack s true ++ callMetadata c ++ [(preemptCountAddress.toNat,4)]) = true
  countApart : spansApart (countSpans names o)
    (callStack s true ++ callServices c ++ trieSpans names o) = true
  preemptApart : spansApart (callStack s true ++ callMetadata c ++ callHeaders c) [(preemptCountAddress.toNat,4)] = true

theorem callFrameCheck_sound {names o c s ra bits key}
    (checked : callFrameCheck names o c s ra bits key = .ok ()) : CallFacts names o c s ra bits key := by
  unfold callFrameCheck at checked
  obtain ⟨entry,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨stack,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨input,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨coverage,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨hardirq,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨pending,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨decoderApart,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨queryApart,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨serviceApart,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨bufferApart,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨countApart,checked⟩ := check_ok _ _ _ _ checked
  obtain ⟨preemptApart,_⟩ := check_ok _ _ _ _ checked
  have phases : coverageCheck c s.data.dmem = true ∧ coverageDataCheck ⟨c.coverage,c.preempt+512⟩ s.data.dmem = true := by
    simpa only [Bool.and_eq_true] using coverage
  refine ⟨by simpa [EntryFrame] using entry,
    fun i hi => List.all_eq_true.mp stack i (List.mem_range.mpr hi),
    networkKeyCheck_sound input,coverageCheck_sound phases.1,coverageDataCheck_sound phases.2,
    eq_of_beq hardirq,?_,decoderApart,queryApart,serviceApart,bufferApart,countApart,preemptApart⟩
  intro needed
  simpa only [needed,↓reduceIte,beq_iff_eq] using pending

#print axioms callFrameCheck_sound
end Binary.Pair.Trie
