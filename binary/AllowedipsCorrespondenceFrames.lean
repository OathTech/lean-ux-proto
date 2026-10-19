import SourceAdapter
import AllowedipsCorrespondencePrefix
import AllowedipsCorrespondenceState

namespace Binary.AllowedipsCorrespondence
open Leanux LookupObservation AllowedipsRelation

/-- Lift semantic matching while retaining its exact cursor in the fixed
observed event list. -/
theorem matches_lift_from {A B : LookupObservation.Relation}
    {events seen actual source}
    (matching : MatchesPointsFrom A seen actual source)
    (recorded : events = seen ++ actual)
    (convert : ∀ front point rest mirror,
      events = front ++ point :: rest →
      MatchesPoint A (front ++ [point]) point mirror →
      MatchesPoint B (front ++ [point]) point mirror) :
    MatchesPointsFrom B seen actual source := by
  induction matching with
  | nil => exact .nil
  | @cons seen actual mirror actuals mirrors head rest ih =>
    refine .cons (convert seen actual actuals mirror recorded head) (ih ?_)
    simpa only [List.append_assoc,List.singleton_append] using recorded

/-- Find the actual emitting front and derive its R equation from the
incoming physical relation, source Kernel preservation, and executed frame.
This version covers the neutral search front, before peer acquisition. -/
theorem atPoint_framed (c : Config) (initialRaw : List MachineState)
    (initialSeen : List LookupObservation.Point) (initial : MachineState) (world : World)
    (related : R c initialRaw initialSeen initial world)
    (neutral : PeerCountPhase.scan none initialRaw = none)
    (history : List MachineState) (events front : List LookupObservation.Point)
    (actual : LookupObservation.Point) (rest : List LookupObservation.Point)
    (source : MirrorHistory.Point)
    (observed : AllowedipsObservation.observe c.rxSection history = .ok events)
    (recorded : events = front ++ actual :: rest)
    (kernel : source.world.wg = world.wg)
    (steps : StepsAt c (front ++ [actual]) source.world)
    (prefixNeutral : ∀ n, PeerCountPhase.scan none (history.take n) = none)
    (writes : Address → Prop)
    (frame : EqualOutside writes initial.data.dmem actual.machine.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬writes a) :
    AtPoint (R c) c.rxSection history (front ++ [actual]) actual.machine source.world := by
  have present : events[front.length]? = some actual := by rw [recorded]; simp
  obtain ⟨i,localEvents,presentAt,localObs,count,same,emitted⟩ :=
    observe_locate c.rxSection history events observed front.length actual present
  have taken : events.take (front.length+1) = front ++ [actual] := by
    rw [recorded,List.take_append,List.take_of_length_le (by omega : front.length ≤ front.length+1)]
    simp
  have last : (history.take (i+1)).getLast? = some actual.machine := by
    rw [List.getLast?_take]
    simp [presentAt]
  have phase : LookupRelation.countPhase (history.take (i+1)) (front ++ [actual]) =
      LookupRelation.countPhase initialRaw initialSeen := by
    rw [countPhase_none initialRaw initialSeen neutral]
    exact countPhase_none _ _ (prefixNeutral (i+1))
  refine ⟨i,localEvents,presentAt,localObs,by simp,?_,?_,?_,?_⟩
  · simpa using count
  · simpa only [List.length_append,List.length_singleton,taken] using same
  · rcases emitted with zero | ⟨prior,priorObs,fewer⟩
    · exact .inl zero
    · exact .inr ⟨prior,priorObs,by simp only [List.length_append,List.length_singleton]; omega⟩
  · exact related.frame_kernel c initialRaw (history.take (i+1)) initialSeen (front ++ [actual])
      initial actual.machine world source.world kernel last phase writes frame apart steps

/-- A concrete pre-helper matching bridge. No physical relation at future
points is assumed: the source Kernel is unchanged and actual memory frames
plus the neutral count scanner establish it at the strict emitting prefixes. -/
theorem matches_framed (c : Config) (initialRaw : List MachineState)
    (initialSeen : List LookupObservation.Point) (initial : MachineState) (world : World)
    (related : R c initialRaw initialSeen initial world)
    (neutral : PeerCountPhase.scan none initialRaw = none)
    (history : List MachineState) (events : List LookupObservation.Point)
    (source : List MirrorHistory.Point)
    (observed : AllowedipsObservation.observe c.rxSection history = .ok events)
    (semantic : MatchesPoints (fun seen _ w => StepsAt c seen w ∧ w.wg = world.wg) events source)
    (prefixNeutral : ∀ n, PeerCountPhase.scan none (history.take n) = none)
    (writes : Address → Prop)
    (frames : ∀ p ∈ events, EqualOutside writes initial.data.dmem p.machine.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬writes a) :
    MatchesPoints (AtPoint (R c) c.rxSection history) events source := by
  apply matches_lift_from semantic (show events = [] ++ events from rfl)
  intro front actual rest mirror recorded point
  refine ⟨point.1,?_,point.2.2⟩
  exact atPoint_framed c initialRaw initialSeen initial world related neutral history events front
    actual rest mirror observed recorded point.2.1.2 point.2.1.1 prefixNeutral writes
    (frames actual (by rw [recorded]; simp)) apart

#print axioms atPoint_framed
#print axioms matches_framed
end Binary.AllowedipsCorrespondence
