import Leanux.Proofs.Logged.PrefixLoops

/-! A certificate for every journal prefix is separate from safety of its
last entry. Extension certificates retain all newly crossed event positions.
This is a logical history certificate, not a native execution-cut relation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
open Leanux Leanux.Proofs.Logged

def All (Safe : List E→Prop) (history : List E) : Prop :=
  ∀ n, n≤history.length → Safe (history.take n)

def Cuts (Safe : List E→Prop) (before suffix : List E) : Prop :=
  ∀ n, n≤suffix.length → Safe (before ++ suffix.take n)

theorem All.last (before : All Safe history) : Safe history := by
  simpa only [List.take_length] using before history.length (Nat.le_refl _)

theorem All.nil (safe : Safe []) : All Safe [] := by
  intro n bound
  simpa using safe

theorem Cuts.nil (safe : Safe history) : Cuts Safe history [] := by
  intro n bound
  simpa using safe

theorem Cuts.last (before : Cuts Safe history suffix) : Safe (history++suffix) := by
  simpa only [List.take_length] using before suffix.length (Nat.le_refl _)

theorem Cuts.singleton (before : Safe history) (after : Safe (history++[event])) :
    Cuts Safe history [event] := by
  intro n bound
  have choices : n=0 ∨ n=1 := by have small : n≤1 := bound; omega
  rcases choices with rfl | rfl
  · simpa using before
  · simpa using after

theorem All.append (before : All Safe history) (added : Cuts Safe history suffix) :
    All Safe (history++suffix) := by
  intro n bound
  by_cases early : n≤history.length
  · rw [List.take_append_of_le_length early]
    exact before n early
  · rw [List.take_append,List.take_of_length_le (by omega : history.length≤n)]
    apply added
    simp only [List.length_append] at bound
    omega

theorem Cuts.append (first : Cuts Safe history left) (second : Cuts Safe (history++left) right) :
    Cuts Safe history (left++right) := by
  intro n bound
  by_cases early : n≤left.length
  · rw [List.take_append_of_le_length early]
    exact first n early
  · rw [List.take_append,List.take_of_length_le (by omega : left.length≤n),←List.append_assoc]
    apply second
    simp only [List.length_append] at bound
    omega

/-- Extraction names the exact prefix position, including the empty prefix. -/
theorem All.at_prefix (before : All Safe history) (position : history=earlier++suffix) : Safe earlier := by
  subst history
  simpa only [List.take_append_length] using
    before earlier.length (by simp only [List.length_append]; omega)

theorem All.take (before : All Safe history) (n : Nat) : All Safe (history.take n) := by
  intro k bound
  rw [List.take_take]
  apply before
  simp only [List.length_take] at bound
  omega

/-- A quiet-append rule must preserve the chosen safety predicate at each
new event; terminal or birth effects cannot use this rule merely by erasure. -/
theorem Cuts.quiet {Safe : List E→Prop} {Quiet : E→Prop} (before : Safe history) (quiet : ∀ event∈suffix, Quiet event)
    (step : ∀ h event, Safe h→Quiet event→Safe (h++[event])) : Cuts Safe history suffix := by
  induction suffix generalizing history with
  | nil => exact Cuts.nil before
  | cons event rest ih =>
    have head := Cuts.singleton before (step history event before (quiet event (by simp)))
    have tail := ih (history:=history++[event]) head.last (by
      intro e member
      exact quiet e (by simp [member]))
    simpa only [List.singleton_append] using head.append tail

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix
