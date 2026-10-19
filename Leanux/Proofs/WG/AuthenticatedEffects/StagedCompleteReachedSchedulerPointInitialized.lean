import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointEntries
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedScheduleCaller

/-! Existing initialized scheduler callers supply the carrier for canonical
native points. The committed worker and NAPI child contracts remain visible;
each constructed remainder is transported through the actual runner caller. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
open Scheduler.Points
variable {native inside : ChildPoints} {Good : Scheduler.Points.History → World → Prop}

theorem Entry.source_points
    (entry : Entry trace placeholders operationIndex world history)
    (carrierGood : ∀ h w, CompleteProduct.Carrier h w → Good h w)
    (children : ChildContracts native inside Good) :
    Covered native Good (scheduleShape none) world history ∧
      Remainders children (scheduleShape none) world history := by
  have complete := schedule_covered carrierGood children none entry.carrier
    (result:=(runPrefix (Driver.scheduleObserved hooks none) world history).1)
    (last:=(runPrefix (Driver.scheduleObserved hooks none) world history).2) rfl
  exact complete.2

theorem Entry.source_point_continuation
    (entry : Entry trace placeholders operationIndex world history)
    (children : ChildContracts native inside Good)
    (point : Point native (scheduleShape none) world history site v after) :
    ∃ remaining, Residual children (scheduleShape none) world history site v after remaining ∧
      runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
        (fun result w=>(result,w)) trace placeholders) [] =
        runPrefixOuter (entry.resume v remaining) after := by
  obtain ⟨remaining,residual⟩ := point.residual children
  refine ⟨remaining,residual,?_⟩
  rw [entry.original]
  exact entry.resume_run_eq _ _ residual.run

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
