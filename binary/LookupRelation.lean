import LookupProjection
import OwnerPending
import PeerCountPhase
import BucketWorlds

namespace Binary.LookupRelation
open Leanux Leanux.WG

theorem project_steps (c : Config) (world : World) (steps : Array Step) :
    project c {world with ambient := {world.ambient with steps}} = project c world := rfl

theorem project_advance (c : Config) (world : World) (steps : List Step) :
    project c (LookupSearch.advance world steps) = project c world := by
  rw [LookupSearch.advance_eq]
  rfl

theorem helperActive_call (seen : List LookupObservation.Point) (s : MachineState) :
    helperActive (seen ++ [LookupObservation.call "wg_peer_get_maybe_zero" s]) = true := by
  simp [helperActive, helperTag, LookupObservation.call]

theorem helperActive_return (seen : List LookupObservation.Point) (s : MachineState) :
    helperActive (seen ++ [LookupObservation.returned "wg_peer_get_maybe_zero" s]) = false := by
  simp [helperActive, helperTag, LookupObservation.returned]

theorem helperActive_decision (seen : List LookupObservation.Point) (rx : Nat)
    (d : Decision) (b : Bool) (s : MachineState) (operands : Option (Int × Int)) :
    helperActive (seen ++ [LookupObservation.decision rx d b s operands]) = helperActive seen := by
  simp [helperActive, helperTag, LookupObservation.decision]

theorem countPhase_inactive (raw : List MachineState) (seen : List LookupObservation.Point)
    (inactive : helperActive seen = false) : countPhase raw seen = none := by
  simp [countPhase, inactive]

theorem ownerPending_outer_return (seen : List LookupObservation.Point)
    (s current : MachineState) :
    ownerPending (seen ++ [LookupObservation.returned "wg_index_hashtable_lookup" s]) current = none := by
  unfold ownerPending
  split <;> simp [lastHelperReturn, LookupObservation.returned]

theorem helperActive_append_decisions (seen delta : List LookupObservation.Point)
    (tags : LookupHistory.DecisionPoints delta) :
    helperActive (seen ++ delta) = helperActive seen := by
  induction delta generalizing seen with
  | nil => simp
  | cons point rest ih =>
    obtain ⟨step, _, tag⟩ := tags point (by simp)
    have tail := ih (seen ++ [point]) (fun q member => tags q (by simp [member]))
    simpa [List.append_assoc, helperActive, helperTag, tag] using tail

theorem lastHelperReturn_append_decisions (seen delta : List LookupObservation.Point)
    (tags : LookupHistory.DecisionPoints delta)
    (initial : lastHelperReturn seen = none) :
    lastHelperReturn (seen ++ delta) = none := by
  induction delta generalizing seen with
  | nil => simpa using initial
  | cons point rest ih =>
    obtain ⟨step, _, tag⟩ := tags point (by simp)
    have next : lastHelperReturn (seen ++ [point]) = none := by
      simp [lastHelperReturn, tag]
    simpa only [List.append_assoc, List.singleton_append] using
      ih (seen ++ [point]) (fun q member => tags q (by simp [member])) next

theorem ownerPending_none (seen : List LookupObservation.Point) (s : MachineState)
    (noReturn : lastHelperReturn seen = none) : ownerPending seen s = none := by
  unfold ownerPending
  split <;> simp [noReturn]

/-- Ordinary-phase frame, used by the bucket walk. Helper activity and
    pending-owner mode are established from its actual decision prefixes,
    while every physical equation follows from the instruction write frame. -/
theorem Physical.frame_inactive (c : Config) (raw raw' : List MachineState)
    (seen seen' : List LookupObservation.Point) (s t : MachineState) (v : View)
    (represented : Physical c raw seen s v)
    (inactive : helperActive seen = false) (inactive' : helperActive seen' = false)
    (ordinary : ownerPending seen s = none) (ordinary' : ownerPending seen' t = none)
    (writes : Address → Prop) (same : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ address, Reads c v address → ¬writes address) :
    Physical c raw' seen' t v := by
  obtain ⟨selection, ⟨head, loaded, bucket⟩, owner, count⟩ := represented
  refine ⟨selection, ⟨head, ?_, ?_⟩, ?_, ?_⟩
  · exact (same.loadInt _ 8 (fun i hi => apart _ (.inl ⟨i, hi, rfl⟩))).symm.trans loaded
  · apply BucketShape.frame_reads same _ _ head bucket
    intro cell member address read
    obtain ⟨e, memberE, eq⟩ := List.mem_map.mp member
    subst cell
    exact apart address (.inr (.inl ⟨e, memberE, read⟩))
  · cases focus : c.focus.owner with
    | none => simpa only [focus] using owner
    | some id =>
      simp only [focus] at owner ⊢
      obtain ⟨word, value, field⟩ := owner
      refine ⟨word, value, ?_⟩
      simp only [OwnerFieldAt, ordinary] at field
      simp only [OwnerFieldAt, ordinary']
      exact OwnerWord.Field.frame same
        (fun i hi => apart _ (.inr (.inr (.inl ⟨id, focus, i, hi, rfl⟩)))) field
  · cases focus : c.focus.peer with
    | none => simpa only [focus] using count
    | some id =>
      simp only [focus] at count ⊢
      obtain ⟨number, value, nonnull, field⟩ := count
      refine ⟨number, value, nonnull, ?_⟩
      rw [countPhase_inactive _ _ inactive] at field
      rw [countPhase_inactive _ _ inactive']
      exact PeerCountPhase.At.frame same
        (fun i hi => apart _ (.inr (.inr (.inr ⟨id, focus, i, hi, rfl⟩)))) field

theorem StepsAt.advance (c : Config) (seen delta : List LookupObservation.Point)
    (world : World) (represented : StepsAt c seen world) :
    StepsAt c (seen ++ delta) (LookupSearch.advance world (delta.filterMap (·.step))) := by
  rw [LookupSearch.advance_eq]
  constructor
  · simpa [List.filterMap_append, List.append_assoc] using
      congrArg (fun xs => xs ++ delta.filterMap (·.step)) represented.1
  · exact represented.2

theorem R.advance_inactive (c : Config) (raw raw' : List MachineState)
    (seen delta : List LookupObservation.Point) (s t : MachineState) (world : World)
    (related : R c raw seen s world)
    (last : raw'.getLast? = some t)
    (tags : LookupHistory.DecisionPoints delta)
    (inactive : helperActive seen = false)
    (noReturn : lastHelperReturn seen = none)
    (writes : Address → Prop) (same : EqualOutside writes s.data.dmem t.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ address, Reads c v address → ¬writes address) :
    R c raw' (seen ++ delta) t
      (LookupSearch.advance world (delta.filterMap (·.step))) := by
  obtain ⟨_, ⟨v, projected, physical⟩, steps⟩ := related
  refine ⟨last, ⟨v, ?_, ?_⟩, steps.advance c seen delta world⟩
  · simpa only [project_advance] using projected
  · apply physical.frame_inactive c raw raw' seen (seen ++ delta) s t v
      inactive (by rw [helperActive_append_decisions _ _ tags, inactive])
      (ownerPending_none _ _ noReturn)
      (ownerPending_none _ _ (lastHelperReturn_append_decisions _ _ tags noReturn))
      writes same (apart v projected)

#print axioms R.advance_inactive
#print axioms helperActive_append_decisions
#print axioms lastHelperReturn_append_decisions
#print axioms Physical.frame_inactive
#print axioms StepsAt.advance
#print axioms project_advance
#print axioms helperActive_call
#print axioms helperActive_return
#print axioms helperActive_decision
#print axioms countPhase_inactive
#print axioms ownerPending_outer_return
end Binary.LookupRelation
