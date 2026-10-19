import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationPointScheduler
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointInitialized

/-! The initialized scheduler now uses the concrete canonical iteration
source. Remaining iteration children and NAPI are explicit same-execution
contracts, and every selected point keeps the original runner continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
open Iteration.Points
variable {native inside : Iteration.Points.ChildPoints}
  {nativeNapi insideNapi : NapiPoints} {Good : Iteration.Points.History → World → Prop}

theorem Entry.iteration_source_points
    (entry : Entry trace placeholders operationIndex world history)
    (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : Iteration.Points.ChildContracts native inside Good)
    (napi : Scheduler.Points.ChildSourceContract (schedulerPoints native nativeNapi)
      (schedulerPoints inside insideNapi) Good .napi) :
    Scheduler.Points.Covered (schedulerPoints native nativeNapi) Good
      (Scheduler.Points.scheduleShape none) world history ∧
    Scheduler.Points.Remainders (scheduler_children carrierGood children napi)
      (Scheduler.Points.scheduleShape none) world history :=
  entry.source_points carrierGood (scheduler_children carrierGood children napi)

theorem Entry.iteration_point_continuation
    (entry : Entry trace placeholders operationIndex world history)
    (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : Iteration.Points.ChildContracts native inside Good)
    (napi : Scheduler.Points.ChildSourceContract (schedulerPoints native nativeNapi)
      (schedulerPoints inside insideNapi) Good .napi)
    (point : Scheduler.Points.Point (schedulerPoints native nativeNapi)
      (Scheduler.Points.scheduleShape none) world history site v after) :
    ∃ remaining, Scheduler.Points.Residual (scheduler_children carrierGood children napi)
        (Scheduler.Points.scheduleShape none) world history site v after remaining ∧
      runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
        (fun result w=>(result,w)) trace placeholders) [] =
        runPrefixOuter (entry.resume v remaining) after :=
  entry.source_point_continuation (scheduler_children carrierGood children napi) point

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
