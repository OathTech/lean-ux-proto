import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDrainInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationInitialized

/-! Fixed initialized scheduler callers: the crypt suffix after transmit,
and the scheduler following an actual send-drain iteration. Every branch
retains the source-selected loop position and original return continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

inductive Entry (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (world : World) (history : List Event) : Type where
  | afterXmit (entry : ScheduledRun.Entry trace placeholders operationIndex world history)
  | sendDrain {callerWorld callerHistory}
      (caller : SendRun.Entry trace placeholders operationIndex callerWorld callerHistory)
      (path : SendDrain.SchedulePath callerWorld callerHistory world history)

def Entry.resume (entry : Entry trace placeholders operationIndex world history)
    (w : World) (body : PrefixM Event Unit) : PrefixOuter Event (Lean.Json×World) :=
  match entry with
  | .afterXmit source => AfterXmit.resume trace operationIndex source.caller.path.op
      source.caller.path.state source.caller.path.ret w (do body; AfterXmit.afterScheduled)
  | .sendDrain caller path => caller.resume w (do body; SendDrain.remaining path.worker.rest)

theorem Entry.carrier (entry : Entry trace placeholders operationIndex world history) :
    CompleteProduct.Carrier history world := by
  cases entry with
  | afterXmit source => exact source.carrier
  | sendDrain caller path => exact path.carrier caller.carrier

theorem Entry.original (entry : Entry trace placeholders operationIndex world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume world (Driver.scheduleObserved hooks none)) history := by
  cases entry with
  | afterXmit source => exact source.original
  | sendDrain caller path =>
      rw [caller.original]
      exact caller.resume_run_eq _ _ path.continuation

theorem Entry.resume_run_eq (entry : Entry trace placeholders operationIndex world history)
    (left right : PrefixM Event Unit) (same : runPrefix left w before=runPrefix right v after) :
    runPrefixOuter (entry.resume w left) before=runPrefixOuter (entry.resume v right) after := by
  cases entry with
  | afterXmit source =>
      apply AfterXmit.resume_run_eq
      exact Scheduler.bind_run_equal (fun _=>AfterXmit.afterScheduled) same
  | sendDrain caller path =>
      apply caller.resume_run_eq
      exact Scheduler.bind_run_equal (fun _=>SendDrain.remaining path.worker.rest) same

structure Iteration (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (active : Activation) (world : World) (history : List Event) where
  schedulerWorld : World
  schedulerHistory : List Event
  entry : Entry trace placeholders operationIndex schedulerWorld schedulerHistory
  path : Scheduler.IterationPath none schedulerWorld schedulerHistory active world history

def Iteration.resume (cut : Iteration trace placeholders operationIndex active world history)
    (w : World) (body : PrefixM Event IterResult) : PrefixOuter Event (Lean.Json×World) :=
  cut.entry.resume w (body >>= cut.path.afterIteration)

theorem Iteration.carrier (cut : Iteration trace placeholders operationIndex active world history) :
    CompleteProduct.Carrier history world := cut.path.carrier cut.entry.carrier

theorem Iteration.original (cut : Iteration trace placeholders operationIndex active world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (cut.resume world (Driver.iterationObserved hooks active)) history := by
  rw [cut.entry.original]
  exact cut.entry.resume_run_eq _ _ cut.path.continuation

theorem Iteration.resume_run_eq (cut : Iteration trace placeholders operationIndex active world history)
    (left right : PrefixM Event IterResult) (same : runPrefix left w before=runPrefix right v after) :
    runPrefixOuter (cut.resume w left) before=runPrefixOuter (cut.resume v right) after :=
  cut.entry.resume_run_eq _ _ (Scheduler.bind_run_equal cut.path.afterIteration same)

theorem Iteration.accounted (cut : Iteration trace placeholders operationIndex active world history) :
    ∃ ledger, CompleteConsequences.Cut history ledger [] [] world.wg := by
  obtain ⟨ledger,before⟩ := cut.carrier.1
  exact ⟨ledger,CompleteConsequences.accounted before⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
