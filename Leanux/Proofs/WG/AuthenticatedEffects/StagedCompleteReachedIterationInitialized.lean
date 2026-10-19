import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedScheduledInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerIteration

/-! A concrete scheduler selection and literal run-loop prefix connect an
actual activation entry to the initialized trace. The entire remaining
activation, scheduler and return-to-user continuation is preserved. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

structure Iteration (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (active : Activation) (world : World) (history : List Event) where
  schedulerWorld : World
  schedulerHistory : List Event
  entry : Entry trace placeholders operationIndex schedulerWorld schedulerHistory
  path : Scheduler.IterationPath none schedulerWorld schedulerHistory active world history

theorem Iteration.carrier (cut : Iteration trace placeholders operationIndex active world history) :
    CompleteProduct.Carrier history world := cut.path.carrier cut.entry.carrier

def Iteration.next (cut : Iteration trace placeholders operationIndex active world history)
    (result : IterResult) : PrefixM Event Unit := do
  cut.path.afterIteration result
  AfterXmit.afterScheduled

theorem Iteration.original (cut : Iteration trace placeholders operationIndex active world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (AfterXmit.resume trace operationIndex cut.entry.caller.path.op
        cut.entry.caller.path.state cut.entry.caller.path.ret world
        (Driver.iterationObserved hooks active >>= cut.next)) history := by
  rw [cut.entry.original]
  apply AfterXmit.resume_run_eq
  unfold Iteration.next
  simpa only [bind_assoc] using
    Scheduler.bind_run_equal (fun _=>AfterXmit.afterScheduled) cut.path.continuation

theorem Iteration.accounted (cut : Iteration trace placeholders operationIndex active world history) :
    ∃ ledger, CompleteConsequences.Cut history ledger [] [] world.wg := by
  obtain ⟨ledger,before⟩ := cut.carrier.1
  exact ⟨ledger,CompleteConsequences.accounted before⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledRun
