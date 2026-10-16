import AllowedipsCorrespondenceFrames

namespace Binary.AllowedipsCorrespondence
open Leanux LookupObservation AllowedipsRelation

/-- Nonempty matching identifies the latest source World from the same
    matched event prefix, even when several events share one machine edge. -/
theorem matched_last {Q : LookupObservation.Relation} {seen actual source}
    (matching : MatchesPointsFrom Q seen actual source) (nonempty : actual ≠ []) :
    ∃ point mirror, actual.getLast? = some point ∧ source.getLast? = some mirror ∧
      MatchesPoint Q (seen ++ actual) point mirror := by
  induction matching with
  | nil => exact False.elim (nonempty rfl)
  | @cons seen point mirror actual source head rest ih =>
    cases actual with
    | nil =>
      have empty : source = [] := List.length_eq_zero_iff.mp (by simpa using rest.length_eq.symm)
      subst source
      exact ⟨point,mirror,rfl,rfl,head⟩
    | cons next remaining =>
      obtain ⟨lastPoint,lastMirror,actualLast,sourceLast,related⟩ := ih (by simp)
      refine ⟨lastPoint,lastMirror,?_,?_,?_⟩
      · simpa using actualLast
      · have sourceNonempty : source ≠ [] := by
          intro empty
          simp [empty] at sourceLast
        simp only [List.getLast?_cons,sourceLast,Option.getD_some]
      · simpa only [List.append_assoc,List.singleton_append] using related

/-- Successful lookup observation always includes its actual entry call. -/
theorem observe_nonempty (rx : Nat) (history : List MachineState) (events : List Point)
    (observed : AllowedipsObservation.observe rx history = .ok events) : events ≠ [] := by
  cases history with
  | nil => cases observed
  | cons initial tail =>
    by_cases pc : initial.pc = AllowedipsImage.Lookup.entry
    · cases raw : observeHistory (AllowedipsObservation.edge rx) (initial :: tail) with
      | error error => simp [AllowedipsObservation.observe,pc,raw] at observed; cases observed
      | ok actual =>
        have same : call "lookup" initial :: actual = events := by
          simp only [AllowedipsObservation.observe,pc,bne_self_eq_false,Bool.false_eq_true,↓reduceIte,raw] at observed
          exact Except.ok.inj observed
        rw [←same]
        simp
    · simp [AllowedipsObservation.observe,pc] at observed; cases observed

/-- Lift a neutral search prefix's memory frames to R at all stuttering
    cuts. The latest World and its decision log come from the exact matched
    source prefix; no cut-specific source history is supplied. -/
theorem cuts_framed (c : Config) (initialRaw : List MachineState)
    (initialSeen : List Point) (initial : MachineState) (world : World)
    (related : R c initialRaw initialSeen initial world)
    (neutral : PeerCountPhase.scan none initialRaw = none)
    (history : List MachineState) (events : List Point) (source : List MirrorHistory.Point)
    (observed : AllowedipsObservation.observe c.rxSection history = .ok events)
    (matched : MatchesPoints (AtPoint (R c) c.rxSection history) events source)
    (sourceKernel : ∀ point ∈ source, point.world.k = world.k)
    (prefixNeutral : ∀ n, PeerCountPhase.scan none (history.take n) = none)
    (writes : Address → Prop)
    (frames : ∀ current ∈ history, Cut current.pc →
      EqualOutside writes initial.data.dmem current.data.dmem)
    (apart : ∀ v, project c world = some v → ∀ a, Reads c v a → ¬writes a) :
    CutsAligned (R c) c.rxSection history source := by
  apply CutsAligned.of_points matched observed
  intro i current present cut
  have rawNonempty : history.take (i+1) ≠ [] := by
    have bound := (List.getElem?_eq_some_iff.mp present).1
    intro empty
    have length := congrArg List.length empty
    simp only [List.length_take,List.length_nil] at length
    omega
  have restored := List.take_append_drop (i+1) history
  obtain ⟨localEvents,rest,localObs,_⟩ := observe_prefix c.rxSection
    (history.take (i+1)) (history.drop (i+1)) events
    (by simpa only [restored] using observed) rawNonempty
  have matching := prefix_matched
    (front := history.take (i+1)) (tail := history.drop (i+1))
    (by simpa only [restored] using matched) (by simpa only [restored] using observed) localObs
  obtain ⟨point,mirror,_,sourceLast,pointMatched⟩ :=
    matched_last matching.2 (observe_nonempty _ _ _ localObs)
  have worldMember : mirror ∈ source :=
    List.mem_of_mem_take (List.mem_of_getLast? sourceLast)
  obtain ⟨_,_,_,pointR⟩ := pointMatched.2.1.last
  have steps : StepsAt c localEvents mirror.world := by
    simpa only [List.nil_append] using pointR.2.2
  have last : (history.take (i+1)).getLast? = some current := by
    rw [List.getLast?_take]
    simp [present]
  have phase : LookupRelation.countPhase (history.take (i+1)) localEvents =
      LookupRelation.countPhase initialRaw initialSeen := by
    rw [countPhase_none initialRaw initialSeen neutral]
    exact countPhase_none _ _ (prefixNeutral (i+1))
  refine ⟨localEvents,mirror,localObs,sourceLast,?_⟩
  exact related.frame_kernel c initialRaw (history.take (i+1)) initialSeen localEvents initial current
    world mirror.world (sourceKernel mirror worldMember) last phase writes
    (frames current (List.mem_of_getElem? present) cut) apart steps

#print axioms cuts_framed
end Binary.AllowedipsCorrespondence
