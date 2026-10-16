import AllowedipsObservation
import ExecutedCorrespondence

namespace Binary.AllowedipsCorrespondence
open Leanux LookupObservation

private abbrev observe := AllowedipsObservation.observe

/-- All lookup/common_bits cuts and the anchored peer-get cuts. -/
def Cut (pc : Int64) : Prop :=
  pc ∈ AllowedipsImage.cutPoints ∨
    (pc ∈ Image.cutPoints ∧ (Image.fetchIn Image.PeerGet.entry Image.PeerGet.code pc).isSome = true)

/-- The raw prefix is the actual instruction history at this point. The
    event prefix additionally selects the source phase on compiler-merged
    edges. Neither argument is supplied by an expected source execution. -/
abbrev Relation := List MachineState → List Point → MachineState → World → Prop

/-- Locate a semantic point at the edge that emitted it, inside the fixed
    executed history. The preceding prefix has strictly fewer events than
    `seen`, so a later recurrence of the same state/events cannot stand in for
    the emitting edge. Two decisions emitted by one edge use the same raw
    prefix and distinct `seen` prefixes. No arbitrary history is existentially
    supplied: the only choice is an index in this executed list. -/
def AtPoint (R : Relation) (rxSection : Nat) (history : List MachineState)
    (seen : List Point) (current : MachineState) (world : World) : Prop :=
  ∃ index events,
    history[index]? = some current ∧
    observe rxSection (history.take (index + 1)) = .ok events ∧
    seen ≠ [] ∧ seen.length ≤ events.length ∧ seen = events.take seen.length ∧
    (index = 0 ∨ ∃ earlier, observe rxSection (history.take index) = .ok earlier ∧
      earlier.length < seen.length) ∧
    R (history.take (index + 1)) seen current world

/-- Extension preserves an old point's exact raw prefix, for arbitrary R. -/
theorem AtPoint.append {R rxSection history seen current world}
    (related : AtPoint R rxSection history seen current world) (tail : List MachineState) :
    AtPoint R rxSection (history ++ tail) seen current world := by
  obtain ⟨i, events, present, observed, nonempty, bound, prefixEq, emitted, represented⟩ := related
  have hi := (List.getElem?_eq_some_iff.mp present).1
  have takeNext : (history ++ tail).take (i + 1) = history.take (i + 1) := by
    simp [List.take_append, Nat.sub_eq_zero_of_le (show i + 1 ≤ history.length by omega)]
  have takeBefore : (history ++ tail).take i = history.take i := by
    simp [List.take_append, Nat.sub_eq_zero_of_le (show i ≤ history.length by omega)]
  refine ⟨i, events, ?_, ?_, nonempty, bound, prefixEq, ?_, ?_⟩
  · simpa only [List.getElem?_append_left hi] using present
  · simpa only [takeNext] using observed
  · simpa only [takeBefore] using emitted
  · simpa only [takeNext] using represented

theorem matched_append_history {R rxSection history seen actual source}
    (matched : MatchesPointsFrom (AtPoint R rxSection history) seen actual source)
    (tail : List MachineState) :
    MatchesPointsFrom (AtPoint R rxSection (history ++ tail)) seen actual source := by
  induction matched with
  | nil => exact .nil
  | cons head rest ih =>
    exact .cons ⟨head.1, head.2.1.append tail, head.2.2⟩ ih

/-- Stuttering cuts use their exact raw prefix, including silent arithmetic
    and stores. Semantic matching of the fixed source prefix is retained;
    merely counting events is not enough to choose a source World. -/
def CutsAligned (R : Relation) (rxSection : Nat)
    (history : List MachineState) (source : List MirrorHistory.Point) : Prop :=
  ∀ i current, history[i]? = some current → Cut current.pc →
    ∃ events last,
      observe rxSection (history.take (i + 1)) = .ok events ∧
      PrefixMatches (AtPoint R rxSection (history.take (i + 1))) events source ∧
      (source.take events.length).getLast? = some last ∧
      R (history.take (i + 1)) events current last.world

theorem CutsAligned.snoc {R rxSection history source}
    (aligned : CutsAligned R rxSection history source) (next : MachineState)
    (newCut : Cut next.pc →
      ∃ events last,
        observe rxSection (history ++ [next]) = .ok events ∧
        PrefixMatches (AtPoint R rxSection (history ++ [next])) events source ∧
        (source.take events.length).getLast? = some last ∧
        R (history ++ [next]) events next last.world) :
    CutsAligned R rxSection (history ++ [next]) source := by
  intro i current present cut
  by_cases old : i < history.length
  · have hp : history[i]? = some current := by
      simpa only [List.getElem?_append_left old] using present
    have result := aligned i current hp cut
    simpa [List.take_append, Nat.sub_eq_zero_of_le (show i + 1 ≤ history.length by omega)] using result
  · have bound := (List.getElem?_eq_some_iff.mp present).1
    have hi : i = history.length := by
      simp only [List.length_append, List.length_singleton] at bound
      omega
    subst i
    have hc : next = current := by simpa using present
    subst current
    rw [List.take_of_length_le (by simp)]
    exact newCut cut

theorem CutsAligned.prefix {R rxSection front tail source}
    (aligned : CutsAligned R rxSection (front ++ tail) source) :
    CutsAligned R rxSection front source := by
  intro i current present cut
  have bound := (List.getElem?_eq_some_iff.mp present).1
  have extended : (front ++ tail)[i]? = some current := by
    simpa only [List.getElem?_append_left bound] using present
  have result := aligned i current extended cut
  simpa [List.take_append, Nat.sub_eq_zero_of_le (show i + 1 ≤ front.length by omega)] using result

theorem CutsAligned.append_source {R rxSection history source}
    (aligned : CutsAligned R rxSection history source) (tail : List MirrorHistory.Point) :
    CutsAligned R rxSection history (source ++ tail) := by
  intro i current present cut
  obtain ⟨events, last, observed, matched, latest, related⟩ := aligned i current present cut
  have takeEq : (source ++ tail).take events.length = source.take events.length :=
    List.take_append_of_le_length matched.1
  refine ⟨events, last, observed, ⟨?_, ?_⟩, ?_, related⟩
  · have bound := matched.1
    simp only [List.length_append]
    omega
  · simpa only [takeEq] using matched.2
  · simpa only [takeEq] using latest

theorem CutsAligned.append_no_cuts {R rxSection history source}
    (aligned : CutsAligned R rxSection history source) (tail : List MachineState)
    (noCuts : ∀ s ∈ tail, ¬Cut s.pc) :
    CutsAligned R rxSection (history ++ tail) source := by
  induction tail generalizing history with
  | nil => simpa only [List.append_nil] using aligned
  | cons s tail ih =>
    have next := aligned.snoc s (fun cut => False.elim (noCuts s (by simp) cut))
    simpa only [List.append_assoc, List.singleton_append] using
      ih next (fun t present => noCuts t (by simp [present]))

/-- Service interiors remain in the raw history even when they contain no
    anchored cuts. Only the actual return adds a new R obligation. -/
theorem CutsAligned.service_extension {R rxSection source}
    (front localHistory : List MachineState) (current final : MachineState)
    (aligned : CutsAligned R rxSection (front ++ [current]) source)
    (last : localHistory.getLast? = some final)
    (noCuts : ∀ s ∈ localHistory.dropLast, ¬Cut s.pc)
    (newCut : Cut final.pc →
      ∃ events latest,
        observe rxSection (front ++ localHistory) = .ok events ∧
        PrefixMatches (AtPoint R rxSection (front ++ localHistory)) events source ∧
        (source.take events.length).getLast? = some latest ∧
        R (front ++ localHistory) events final latest.world) :
    CutsAligned R rxSection (front ++ localHistory) source := by
  have restored := Binary.history_restore last
  have interior := aligned.prefix.append_no_cuts localHistory.dropLast noCuts
  have extended := interior.snoc final (by
    intro cut
    simpa only [List.append_assoc, restored] using newCut cut)
  simpa only [List.append_assoc, restored] using extended

/-- Whole-run M2 correspondence for a relation that reads execution history.
    The execution judgment must produce `executed`; this predicate itself
    asserts correspondence, not execution. ABI/result conditions remain
    separate. The semantic-only LookupObservation.MatchesRun is insufficient
    for an R component such as PeerCountPhase.scan. -/
def MatchesRun {α : Type} (R : Relation) (rxSection : Nat)
    (executed : Executed) (source : MirrorHistory.Run α) : Prop :=
  ∃ points, observe rxSection executed.history = .ok points ∧
    MatchesPoints (AtPoint R rxSection executed.history) points source.points ∧
    CutsAligned R rxSection executed.history source.points ∧
    R executed.history points executed.machine source.finalWorld

/-- The raw prefix supplied at a semantic point ends at the actual point.
    This is the prefix on which a pending-store projection starts with none. -/
theorem AtPoint.last {R rxSection history seen current world}
    (related : AtPoint R rxSection history seen current world) :
    ∃ past, past.IsPrefix history ∧ past.getLast? = some current ∧
      R past seen current world := by
  obtain ⟨i, events, present, _, _, _, _, _, represented⟩ := related
  refine ⟨history.take (i + 1), List.take_prefix _ _, ?_, represented⟩
  rw [List.getLast?_take]
  simp [present]

#print axioms CutsAligned.snoc
#print axioms CutsAligned.append_source
#print axioms CutsAligned.prefix
#print axioms CutsAligned.append_no_cuts
#print axioms AtPoint.last
#print axioms AtPoint.append
#print axioms matched_append_history
#print axioms CutsAligned.service_extension
end Binary.AllowedipsCorrespondence
