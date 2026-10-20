import AllowedipsCorrespondenceLocations

namespace Binary.AllowedipsCorrespondence
open Leanux LookupObservation

private abbrev observe := AllowedipsObservation.observe

/-- Strict emission locates an already observed point in this raw prefix,
    even if equal machine states recur later in the full execution. -/
theorem AtPoint.restrict {R rxSection front tail seen current world events}
    (point : AtPoint R rxSection (front ++ tail) seen current world)
    (observed : observe rxSection front = .ok events)
    (bound : seen.length ≤ events.length) :
    AtPoint R rxSection front seen current world := by
  obtain ⟨i, localEvents, present, localObs, nonempty, count, equal, emitted, related⟩ := point
  have frontNonempty : front ≠ [] := by intro empty; subst front; cases observed
  have before : i < front.length := by
    by_cases early : i < front.length
    · exact early
    have later : front.length ≤ i := by omega
    have positive : 0 < front.length := List.length_pos_iff.mpr frontNonempty
    obtain ⟨earlierEvents, earlierObs, fewer⟩ := emitted.resolve_left (by omega)
    have rawBefore : (front ++ tail).take i = front ++ tail.take (i-front.length) := by
      rw [List.take_append, List.take_of_length_le later]
    rw [rawBefore] at earlierObs
    obtain ⟨firstEvents, rest, firstObs, allEq⟩ :=
      observe_prefix rxSection front (tail.take (i-front.length)) earlierEvents earlierObs frontNonempty
    have firstEq : firstEvents = events := Except.ok.inj (firstObs.symm.trans observed)
    rw [firstEq] at allEq
    have sizes := congrArg List.length allEq
    simp only [List.length_append] at sizes
    omega
  have rawNext : (front ++ tail).take (i+1) = front.take (i+1) :=
    List.take_append_of_le_length (by omega)
  have rawBefore : (front ++ tail).take i = front.take i :=
    List.take_append_of_le_length (by omega)
  refine ⟨i, localEvents, ?_, ?_, nonempty, count, equal, ?_, ?_⟩
  · simpa only [List.getElem?_append_left before] using present
  · simpa only [rawNext] using localObs
  · simpa only [rawBefore] using emitted
  · simpa only [rawNext] using related

theorem matched_restrict {R rxSection front tail seen actual source events}
    (matched : MatchesPointsFrom (AtPoint R rxSection (front ++ tail)) seen actual source)
    (observed : observe rxSection front = .ok events)
    (bound : seen.length + actual.length ≤ events.length) :
    MatchesPointsFrom (AtPoint R rxSection front) seen actual source := by
  induction matched with
  | nil => exact .nil
  | @cons seen actual mirror actuals mirrors head rest ih =>
    refine .cons ⟨head.1, head.2.1.restrict observed ?_, head.2.2⟩ (ih ?_)
    · simp only [List.length_append, List.length_singleton]
      simp only [List.length_cons] at bound
      omega
    · simp only [List.length_append,  List.length_cons, List.length_nil] at bound ⊢
      omega

/-- Full point matching restricts to each actual observed raw prefix.
    No new choice of emitting edge or source World is made. -/
theorem prefix_matched {R rxSection front tail events all source}
    (matched : MatchesPoints (AtPoint R rxSection (front ++ tail)) all source)
    (full : observe rxSection (front ++ tail) = .ok all)
    (observed : observe rxSection front = .ok events) :
    PrefixMatches (AtPoint R rxSection front) events source := by
  have nonempty : front ≠ [] := by intro empty; subst front; cases observed
  obtain ⟨localEvents, suffix, localObs, allEq⟩ :=
    observe_prefix rxSection front tail all full nonempty
  have same : localEvents = events := Except.ok.inj (localObs.symm.trans observed)
  rw [same] at allEq
  rw [allEq] at matched
  have prefixed := prefix_of_append matched
  exact ⟨prefixed.1, matched_restrict prefixed.2 observed (by simp)⟩

/-- Composition of semantic point matching and concrete cut-state proofs.
    Execution and the cut-state R facts are supplied by the region proofs;
    this lemma supplies the exact matched source prefix at every cut. -/
theorem CutsAligned.of_points {R rxSection history all source}
    (matched : MatchesPoints (AtPoint R rxSection history) all source)
    (observed : observe rxSection history = .ok all)
    (cuts : ∀ i current, history[i]? = some current → Cut current.pc →
      ∃ events last,
        observe rxSection (history.take (i+1)) = .ok events ∧
        (source.take events.length).getLast? = some last ∧
        R (history.take (i+1)) events current last.world) :
    CutsAligned R rxSection history source := by
  intro i current present cut
  obtain ⟨events, last, localObs, latest, related⟩ := cuts i current present cut
  have restored : history.take (i+1) ++ history.drop (i+1) = history := List.take_append_drop _ _
  have matchPrefix := prefix_matched
    (front := history.take (i+1)) (tail := history.drop (i+1))
    (by simpa only [restored] using matched) (by simpa only [restored] using observed) localObs
  exact ⟨events, last, localObs, matchPrefix, latest, related⟩

#print axioms AtPoint.restrict
#print axioms matched_restrict
#print axioms prefix_matched
#print axioms CutsAligned.of_points
end Binary.AllowedipsCorrespondence
