import PairIndexGeometry

namespace Binary.Pair.IndexLookup
open TrustBase CommonBitsCoverage

theorem needed_phases {coverage preempt v} (needed : LookupBufferNeeded coverage preempt v) :
    (Context.mk coverage preempt).Needed ∨ (Context.mk coverage (preempt+512)).Needed := by
  rcases needed with ⟨mode,before | during⟩ | ⟨mode,_,during⟩
  · exact .inl ⟨before,.inl mode⟩
  · exact .inr ⟨by simpa only [BitVec.add_comm] using during,.inl mode⟩
  · exact .inr ⟨by simpa only [BitVec.add_comm] using during,.inr mode⟩

theorem coverage_of_phases {c : Context} {m : DataMem} {v : LookupRelation.View}
    (before : c.CoverageAt m) (during : (Context.mk c.coverage (c.preempt+512)).CoverageAt m) :
    LookupCoverageAt c.coverage c.preempt v m := by
  refine ⟨before.1,?_,?_,?_⟩
  · rintro (needed | needed)
    · exact before.2.1 needed
    · exact during.2.1 (by simpa only [BitVec.add_comm] using needed)
  · rintro (needed | needed)
    · exact before.2.2.1 needed
    · exact during.2.2.1 (by simpa only [BitVec.add_comm] using needed)
  · intro needed
    rcases needed_phases needed with first | second
    · exact before.2.2.2 first
    · exact during.2.2.2 second

theorem coverage_writes {c : Context} {v : LookupRelation.View} {a : BitVec 64}
    (written : LookupCoverageWrites c.coverage c.preempt v a) : AllowedipsCoverageWrites c.coverage c.preempt a :=
  ⟨needed_phases written.1,written.2⟩

theorem coverage_metadata {c : Context} {v : LookupRelation.View} {a : BitVec 64}
    (read : LookupMetadataBytes c.coverage c.preempt v a) : AllowedipsMetadata c.coverage c.preempt a := by
  rcases read with current | ⟨need,soft⟩ | ⟨need,mode⟩ | ⟨need,buffer⟩
  · exact .inl current
  · exact .inr (.inl ⟨by simpa only [BitVec.add_comm] using need,soft⟩)
  · exact .inr (.inr (.inl ⟨by simpa only [BitVec.add_comm] using need,mode⟩))
  · exact .inr (.inr (.inr (.inl ⟨needed_phases need,buffer⟩)))

theorem coverage_services {c : Context} {v : LookupRelation.View} {a : BitVec 64}
    (read : LookupServiceBytes c.coverage c.preempt v a) :
    AllowedipsServiceBytes c.coverage c.preempt a ∨ InRange preemptCountAddress 4 a := by
  rcases read with metadata | preempt | ⟨need,buffer⟩
  · exact .inl (.inl (coverage_metadata metadata))
  · exact .inr preempt
  · exact .inl (.inr ⟨needed_phases need,buffer⟩)

#print axioms coverage_of_phases
end Binary.Pair.IndexLookup
