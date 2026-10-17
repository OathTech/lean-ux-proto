import Leanux.Proofs.WG.Progress.IdleOperationClaims
import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- An accepted runner operation includes the same actual final wait and
retains its clock and wheel test through ambient stripping and final guards. -/
theorem runnerOperation_final_idle_receipt (trace : Runner.Trace) (state : RunnerAccumulator)
    (op : Runner.Operation)
    (waited : HasFinalIdleWait (Runner.toSyscall state.2.1 state.2.2.1 state.2.1.size op)) (ret : Int) (after : World)
    (run : runnerOperation trace op state = .ok (ret,after)) :
    ∃ seen middle,
      (observedIdleWaitOperation (Runner.toSyscall state.2.1 state.2.2.1 state.2.1.size op)).run (runnerEntry trace state) = .ok ((ret,seen),middle) ∧
      (skipAmbient : Leanux.M Unit).run middle = .ok ((),after) ∧
      (∀ j, seen = some j →
        (Campaign2.Product.snapshot after).wg.jiffiesLast = some j ∧
        NoTimerDue j (Campaign2.Product.snapshot after)) ∧
      RunnerBoundaryClean ⟨state.2.1.size,ret,Campaign2.Product.snapshot after⟩ := by
  obtain ⟨⟨middle,syscallRun,stripped⟩,clean⟩ :=
    runnerOperation_facts trace op state ret after run
  change (syscall (Runner.toSyscall state.2.1 state.2.2.1 state.2.1.size op)).run (runnerEntry trace state) = _ at syscallRun
  rw [← observedIdleWaitOperation_erase _ waited,StateT.run_bind] at syscallRun
  cases observed : (observedIdleWaitOperation (Runner.toSyscall state.2.1 state.2.2.1 state.2.1.size op)).run (runnerEntry trace state) with
  | error stop => rw [observed] at syscallRun; cases syscallRun
  | ok pair =>
    obtain ⟨⟨value,seen⟩,current⟩ := pair
    rw [observed] at syscallRun
    cases syscallRun
    have checked := observedIdleWaitOperation_checks _ (runnerEntry trace state)
      (value,seen) current True.intro observed
    refine ⟨seen,current,rfl,stripped,?_,clean⟩
    intro j same
    obtain ⟨clock,due⟩ := checked j same
    change ((AmbientM.skipAmbient).run current.ambient >>= _) = _ at stripped
    cases ambientRun : AmbientM.skipAmbient.run current.ambient with
    | error stop => rw [ambientRun] at stripped; cases stripped
    | ok pair =>
      obtain ⟨ignored,inputs⟩ := pair
      rw [ambientRun] at stripped
      cases stripped
      exact ⟨clock,due⟩

end Leanux.Proofs.WG.Progress
