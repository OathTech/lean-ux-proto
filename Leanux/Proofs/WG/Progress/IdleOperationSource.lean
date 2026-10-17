import Leanux.Proofs.WG.Progress.IdleOperationModel
import Leanux.Proofs.WG.Progress.AdvanceOperationSource
import Leanux.Proofs.WG.Progress.TimerWaitSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Read-only receipt of the actual wait: absent in recordless mode, otherwise
the clock stored by that same wait. -/
def observedIdleTimers : Leanux.M (Option UInt64) := do
  let recorded := (← getAmbient).hidden.isSome
  idleTimers
  let clock := (← getWG).jiffiesLast
  return if recorded then clock else none

/-- Observing the wait adds no execution, state change or failure. -/
theorem observedIdleTimers_erase :
    (do let _ ← observedIdleTimers; pure ()) = idleTimers := by
  unfold observedIdleTimers
  simp only [bind_assoc,pure_bind]
  funext initial
  change (idleTimers.run initial >>= fun pair => .ok ((),pair.2)) = idleTimers.run initial
  cases waited : idleTimers.run initial with
  | error stop => rfl
  | ok pair => cases pair.1; rfl

/-- Entry, dispatch, return work and pre-wait workers. Under HasFinalIdleWait
this is the actual syscall prefix, with the same network entry resets and guard. -/
def idleWaitOperationPrefix (call : Syscall) : Leanux.M Int := do
  advanceOperationEntry
  let ret ← dispatch call
  for c in Env.windowTailCalls do liftSeccomp (Seccomp.enterHarnessCall c)
  taskWorkRun
  match call with
  | .wgSet _ | .wgInject .. => runSendWorkers
  | .wgXmit .. => afterXmit
  | _ => pure ()
  return ret

/-- Exact original final-wait syscall factor, retaining all prior errors. -/
theorem syscall_final_idle_source (call : Syscall) (waited : HasFinalIdleWait call) :
    syscall call = (do
      let ret ← idleWaitOperationPrefix call
      idleTimers
      pure ret) := by
  cases call <;> simp only [HasFinalIdleWait] at waited
  all_goals try contradiction
  all_goals
    unfold syscall idleWaitOperationPrefix advanceOperationEntry
    simp only [syscallNr,Syscall.isNet,Bool.true_and,bind_assoc]
    congr 1
    funext reset
    congr 1
    funext queued
    congr 1
    funext cleared
    congr 1
    funext task
    split <;> simp only [pure_bind]

/-- Prefix followed by an observed idle wait. Under HasFinalIdleWait, erasure
identifies this computation with the original syscall. -/
def observedIdleWaitOperation (call : Syscall) : Leanux.M (Int × Option UInt64) := do
  let ret ← idleWaitOperationPrefix call
  let seen ← observedIdleTimers
  return (ret,seen)

/-- Erasure preserves each original syscall including every Stop. -/
theorem observedIdleWaitOperation_erase (call : Syscall) (waited : HasFinalIdleWait call) :
    (do let out ← observedIdleWaitOperation call; pure out.1) = syscall call := by
  rw [syscall_final_idle_source call waited]
  unfold observedIdleWaitOperation
  simp only [bind_assoc,pure_bind]
  congr 1
  funext ret
  rw [← observedIdleTimers_erase]
  simp only [bind_assoc,pure_bind]

end Leanux.Proofs.WG.Progress
