import Leanux.Proofs.WG.Progress.AdvanceOperationClaims
import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Leanux.Runner

/-- The runner's accepted wg_advance operation contains this exact decorated
syscall execution, followed by its actual ambient strip and boundary guards.
Concrete execution states remain only in this source-link theorem. -/
theorem runnerOperation_advance_receipt (trace : Trace) (state : RunnerAccumulator)
    (ticks : Nat) (ret : Int) (after : World)
    (run : runnerOperation trace (.wgAdvance ticks) state = .ok (ret,after)) :
    ∃ bounds seen middle,
      (observedAdvanceOperation ticks).run (runnerEntry trace state) = .ok ((ret,bounds,seen),middle) ∧
      (skipAmbient : Leanux.M Unit).run middle = .ok ((),after) ∧
      ret = 0 ∧ (∃ j0 j1, bounds = some (j0,j1) ∧ j1-j0 = ticks.toUInt64 ∧
        ∀ receipt, seen = some receipt → receipt.j0 = j0 ∧ receipt.j1 = j1 ∧
          (Campaign2.Product.snapshot after).wg.jiffiesLast = some receipt.jEnd ∧
          NoTimerDue receipt.pass (Campaign2.Product.snapshot after)) ∧
      RunnerBoundaryClean ⟨state.2.1.size,ret,Campaign2.Product.snapshot after⟩ := by
  obtain ⟨⟨middle,syscallRun,stripped⟩,clean⟩ :=
    runnerOperation_facts trace (.wgAdvance ticks) state ret after run
  change (syscall (.wgAdvance ticks)).run (runnerEntry trace state) = _ at syscallRun
  rw [← observedAdvanceOperation_erase] at syscallRun
  rw [StateT.run_bind] at syscallRun
  cases observed : (observedAdvanceOperation ticks).run (runnerEntry trace state) with
  | error stop => rw [observed] at syscallRun; cases syscallRun
  | ok pair =>
    obtain ⟨⟨value,bounds,seen⟩,current⟩ := pair
    rw [observed] at syscallRun
    cases syscallRun
    obtain ⟨zero,j0,j1,actual,delta,facts⟩ :=
      observedAdvanceOperation_checks ticks (runnerEntry trace state) (value,bounds,seen)
        current True.intro observed
    refine ⟨bounds,seen,current,rfl,stripped,zero,⟨j0,j1,actual,delta,?_⟩,clean⟩
    intro receipt same
    obtain ⟨start,finish,clock,due⟩ := facts receipt same
    change ((AmbientM.skipAmbient).run current.ambient >>= _) = _ at stripped
    cases ambientRun : AmbientM.skipAmbient.run current.ambient with
    | error stop => rw [ambientRun] at stripped; cases stripped
    | ok pair =>
      obtain ⟨ignored,inputs⟩ := pair
      rw [ambientRun] at stripped
      cases stripped
      exact ⟨start,finish,clock,due⟩

end Leanux.Proofs.WG.Progress
