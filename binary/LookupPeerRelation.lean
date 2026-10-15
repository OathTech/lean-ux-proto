import LookupRelation

namespace Binary.LookupRelation
open Leanux Leanux.WG

/-- Helper decisions leave the bucket and owner word untouched. The count
    equation is proved separately from its actual CMPXCHG phase; it is not
    inferred from a frame that permits a count write. -/
theorem Physical.frame_count (c : Config) (raw raw' : List MachineState)
    (seen seen' : List LookupObservation.Point) (s t : MachineState) (v : View)
    (represented : Physical c raw seen s v)
    (ordinary : ownerPending seen s = none) (ordinary' : ownerPending seen' t = none)
    (writes : Address → Prop) (same : EqualOutside writes s.data.dmem t.data.dmem)
    (bucketApart : ∀ a, TrustBase.LookupBucketBytes c v a → ¬writes a)
    (ownerApart : ∀ a, TrustBase.LookupOwnerBytes c a → ¬writes a)
    (countAt : ∀ pid count, c.focus.peer = some pid → v.count = some count →
      PeerCountPhase.At (countPhase raw' seen') t.data.dmem
        (c.peers pid + .ofNat 64 Layouts.peer_refcount) count) :
    Physical c raw' seen' t v := by
  obtain ⟨selection, ⟨head, loaded, bucket⟩, owner, count⟩ := represented
  refine ⟨selection, ⟨head, ?_, ?_⟩, ?_, ?_⟩
  · exact (same.loadInt _ 8 (fun i hi => bucketApart _ (.inl ⟨i, hi, rfl⟩))).symm.trans loaded
  · apply BucketShape.frame_reads same _ _ head bucket
    intro cell member address read
    obtain ⟨e, memberE, eq⟩ := List.mem_map.mp member
    subst cell
    exact bucketApart address (.inr ⟨e, memberE, read⟩)
  · cases focus : c.focus.owner with
    | none => simpa only [focus] using owner
    | some id =>
      simp only [focus] at owner ⊢
      obtain ⟨word, value, field⟩ := owner
      refine ⟨word, value, ?_⟩
      simp only [OwnerFieldAt, ordinary] at field
      simp only [OwnerFieldAt, ordinary']
      exact OwnerWord.Field.frame same
        (fun i hi => ownerApart _ ⟨id, focus, i, hi, rfl⟩) field
  · cases focus : c.focus.peer with
    | none => simpa only [focus] using count
    | some id =>
      simp only [focus] at count ⊢
      obtain ⟨number, value, nonnull, _⟩ := count
      exact ⟨number, value, nonnull, countAt id number focus value⟩

/-- Source decisions retain the kernel state. The target count equation
    must come from the executed helper prefix at that decision or cut. -/
theorem R.advance_count (c : Config) (raw raw' : List MachineState)
    (seen delta : List LookupObservation.Point) (s t : MachineState) (world : World)
    (related : R c raw seen s world) (last : raw'.getLast? = some t)
    (tags : LookupHistory.DecisionPoints delta)
    (noReturn : lastHelperReturn seen = none)
    (writes : Address → Prop) (same : EqualOutside writes s.data.dmem t.data.dmem)
    (bucketApart : ∀ v, project c world = some v →
      ∀ a, TrustBase.LookupBucketBytes c v a → ¬writes a)
    (ownerApart : ∀ a, TrustBase.LookupOwnerBytes c a → ¬writes a)
    (countAt : ∀ v, project c world = some v → ∀ pid count,
      c.focus.peer = some pid → v.count = some count →
      PeerCountPhase.At (countPhase raw' (seen ++ delta)) t.data.dmem
        (c.peers pid + .ofNat 64 Layouts.peer_refcount) count) :
    R c raw' (seen ++ delta) t
      (LookupSearch.advance world (delta.filterMap (·.step))) := by
  obtain ⟨_, ⟨v, projected, physical⟩, steps⟩ := related
  refine ⟨last, ⟨v, ?_, ?_⟩, steps.advance c seen delta world⟩
  · simpa only [project_advance] using projected
  · exact physical.frame_count c raw raw' seen (seen ++ delta) s t v
      (ownerPending_none _ _ noReturn)
      (ownerPending_none _ _ (lastHelperReturn_append_decisions _ _ tags noReturn))
      writes same (bucketApart v projected) ownerApart (countAt v projected)

#print axioms Physical.frame_count
#print axioms R.advance_count
end Binary.LookupRelation
