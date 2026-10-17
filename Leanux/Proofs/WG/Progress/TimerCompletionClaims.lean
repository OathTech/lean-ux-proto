import Leanux.Proofs.WG.Progress.TimerCompletionSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.TimerDiscipline

/-- Every true normal return of the original whole call passes its actual
final queue checks. No callback-success or loop-readiness premise is needed. -/
theorem runTimers_completion (jPass : UInt64) :
    Campaign2.Product.Ensures (Env.runTimers jPass) (fun _ => True)
      (fun result final => result = true → TimerCompletionGuard final) := by
  intro initial result final _ run fired
  subst result
  rw [← runTimers_loop_source] at run
  let start : World := {initial with wg := {initial.wg with queuedThisCall := []}}
  change ((do
    if start.wg.dev.isNone then return false
    let control ← forIn [0:(← recordBudget)] (false,none) (timerOuterTurn jPass)
    timerOuterFinish control).run start) = _ at run
  by_cases absent : start.wg.dev.isNone = true
  · simp only [absent,ite_true] at run
    cases run
  · simp only [absent,Bool.false_eq_true,ite_false] at run
    rw [StateT.run_bind] at run
    cases budgetRun : (recordBudget : Leanux.M Nat).run start with
    | error stop => rw [budgetRun] at run; cases run
    | ok out =>
      obtain ⟨budget,afterBudget⟩ := out
      rw [budgetRun] at run
      change ((forIn [0:budget] (false,none) (timerOuterTurn jPass)).run afterBudget >>= fun out =>
        (timerOuterFinish out.1).run out.2) = _ at run
      cases turns : (forIn [0:budget] (false,none) (timerOuterTurn jPass)).run afterBudget with
      | error stop => rw [turns] at run; cases run
      | ok out =>
        obtain ⟨control,beforeFinish⟩ := out
        rw [turns] at run
        exact timerOuterFinish_completion control beforeFinish true final True.intro run rfl


end Leanux.Proofs.WG.Progress
