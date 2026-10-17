import Leanux.Proofs.WG.Progress.TimerWaitSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- A successful recorded idle wait has no modeled due timer at the actual
end read it stores. This makes no totality or recordless prediction claim. -/
theorem idleTimers_recorded_nothing_due :
    Campaign2.Product.Ensures idleTimers (fun s => s.ambient.hidden.isSome = true)
      (fun _ s => ∃ j, s.wg.jiffiesLast = some j ∧ NoTimerDue j s) := by
  intro initial result final recorded run
  rw [idleTimers_recorded_source initial recorded] at run
  rw [StateT.run_bind] at run
  cases peek : (peekSiteU64 .jiffiesEnd : Leanux.M (Option UInt64)).run initial with
  | error stop => rw [peek] at run; cases run
  | ok pair =>
    obtain ⟨seen,middle⟩ := pair
    rw [peek] at run
    dsimp only [Bind.bind,Except.bind] at run
    cases seen with
    | none => cases run
    | some j =>
      dsimp only at run
      change ((discard (runTimers j)).run middle >>= fun pair =>
        (timerWaitFinish j j).run pair.2) = _ at run
      cases turns : (discard (runTimers j)).run middle with
      | error stop => rw [turns] at run; cases run
      | ok pair =>
        obtain ⟨fired,beforeFinish⟩ := pair
        rw [turns] at run
        exact ⟨j,timerWaitFinish_checks j j beforeFinish result final True.intro run⟩


end Leanux.Proofs.WG.Progress
