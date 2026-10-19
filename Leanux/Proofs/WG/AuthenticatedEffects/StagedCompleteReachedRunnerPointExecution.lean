import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointCanonical

/-! Execution decomposition follows the canonical source witness on both
normal and stopped runs. A failed left operand has no fabricated World. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Leanux Leanux.Proofs.Logged

inductive Execution : {α : Type} → {action : PrefixOuter CausalJournal.Event α} →
    Shape action → History → Result α → History → Prop where
  | pure (value : α) : Execution (.pure value) h (.ok value) h
  | stopped (reason) : Execution (.stopped (α:=α) reason) h (.error reason) h
  | native (token : Native action) (performed : runPrefixOuter action h=(result,last)) :
      Execution (.native token) h result last
  | child (token : Child action)
      (performed : runPrefixOuter (runAtPrefix index w action) h=(result,last)) :
      Execution (.child index w token) h result last
  | failed {body : PrefixOuter CausalJournal.Event α} {next : α → PrefixOuter CausalJournal.Event β}
      {head : Shape body} (tail : ∀value,Shape (next value))
      (leading : Execution head h (.error reason) middle) :
      Execution (.bind head tail) h (.error reason) middle
  | followed {body : PrefixOuter CausalJournal.Event α} {next : α → PrefixOuter CausalJournal.Event β}
      {head : Shape body} {tail : ∀value,Shape (next value)}
      (leading : Execution head h (.ok value) middle)
      (following : Execution (tail value) middle result last) :
      Execution (.bind head tail) h result last
  | marked (label : Label) (w : World) (executed : Execution shape h result last) :
      Execution (.marked label w shape) h result last

theorem Execution.run {shape : Shape action} (executed : Execution shape h result last) :
    runPrefixOuter action h=(result,last) := by
  induction executed with
  | pure => rfl
  | stopped => rfl
  | native _ performed => exact performed
  | child _ performed => exact performed
  | failed _ _ ih => rw [runPrefixOuter_bind,ih]
  | followed _ _ ih₁ ih₂ => rw [runPrefixOuter_bind,ih₁]; exact ih₂
  | marked _ _ _ ih => exact ih

theorem execution_cases (shape : Shape action) (h : History) :
    Execution shape h (runPrefixOuter action h).1 (runPrefixOuter action h).2 := by
  induction shape generalizing h with
  | pure value => exact .pure value
  | stopped reason => exact .stopped reason
  | native token => exact .native token rfl
  | child index w token => exact .child token rfl
  | bind head tail ih₁ ih₂ =>
    rw [runPrefixOuter_bind]
    cases source : runPrefixOuter _ h with
    | mk result middle =>
      have headRun := ih₁ h
      rw [source] at headRun
      cases result with
      | error reason => exact .failed tail headRun
      | ok value => exact .followed headRun (ih₂ value middle)
  | marked label w body ih => exact .marked label w (ih h)

theorem execution_iff (shape : Shape action) :
    Execution shape h result last ↔ runPrefixOuter action h=(result,last) := by
  constructor
  · exact Execution.run
  · intro performed
    have actual := execution_cases shape h
    simpa only [performed] using actual

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
