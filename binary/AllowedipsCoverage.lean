import CommonBitsCalls

namespace Binary.AllowedipsCoverage
open TrustBase CommonBitsCoverage

/-- Both callback phases share physical metadata. Keeping both readings
available permits the BH transition without adding a post-execution premise. -/
def States (coverage : KcovLayout) (old : BitVec 32) (memory : Mem 64) : Prop :=
  AllowedipsCoverageAt coverage old memory ∧ AllowedipsCoverageAt coverage (old+512) memory

theorem metadata_before (coverage : KcovLayout) (old : BitVec 32) (a : BitVec 64)
    (member : (Context.mk coverage old).metadataBytes a) : AllowedipsMetadata coverage old a := by
  rcases member with current | ⟨need,soft⟩ | ⟨need,mode⟩ | ⟨need,buffer⟩
  · exact .inl current
  · exact .inr (.inl ⟨.inl need,soft⟩)
  · exact .inr (.inr (.inl ⟨.inl need,mode⟩))
  · exact .inr (.inr (.inr (.inl ⟨.inl need,buffer⟩)))

theorem metadata_during (coverage : KcovLayout) (old : BitVec 32) (a : BitVec 64)
    (member : (Context.mk coverage (old+512)).metadataBytes a) : AllowedipsMetadata coverage old a := by
  rcases member with current | ⟨need,soft⟩ | ⟨need,mode⟩ | ⟨need,buffer⟩
  · exact .inl current
  · exact .inr (.inl ⟨.inr need,soft⟩)
  · exact .inr (.inr (.inl ⟨.inr need,mode⟩))
  · exact .inr (.inr (.inr (.inl ⟨.inr need,buffer⟩)))

theorem bytes_before (coverage : KcovLayout) (old : BitVec 32) (a : BitVec 64)
    (member : (Context.mk coverage old).bytes a) :
    AllowedipsServiceBytes coverage old a ∨ InRange preemptCountAddress 4 a := by
  rcases member with metadata | preempt | ⟨need,buffer⟩
  · exact .inl (.inl (metadata_before coverage old a metadata))
  · exact .inr preempt
  · exact .inl (.inr ⟨.inl need,buffer⟩)

theorem bytes_during (coverage : KcovLayout) (old : BitVec 32) (a : BitVec 64)
    (member : (Context.mk coverage (old+512)).bytes a) :
    AllowedipsServiceBytes coverage old a ∨ InRange preemptCountAddress 4 a := by
  rcases member with metadata | preempt | ⟨need,buffer⟩
  · exact .inl (.inl (metadata_during coverage old a metadata))
  · exact .inr preempt
  · exact .inl (.inr ⟨.inr need,buffer⟩)

/-- A callback active in one phase preserves the buffer needed in the other.
If inactive, its proved write footprint is empty. -/
theorem other_phase (first second : Context) (same : first.coverage = second.coverage)
    (before after : Mem 64) (old : second.CoverageAt before)
    (new : first.CoverageAt after)
    (frame : EqualOutside first.writes before after)
    (apart : ∀ a, second.metadataBytes a → ¬first.writes a) : second.CoverageAt after := by
  apply coverage_metadata_frame second before after old first.writes frame apart
  intro needed
  by_cases active : first.Needed
  · rw [←same]
    exact (new.2.2.2 active).2.2
  · exact Kcov.buffer_frame second.coverage before after (old.2.2.2 needed).2.2 first.writes frame
      (by intro a h written; exact active written.1)

#print axioms other_phase
end Binary.AllowedipsCoverage
