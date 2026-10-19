import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerEndpoint
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteRunnerClosed

/-! Normal endpoint correspondence uses the World returned by the original
observed runner with its result retained. The history projection is the
original journal. This does not supply a native World at an internal Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open TransmitSecurity RetirementSecurity CausalJournal

theorem normal_ready (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (Queues.RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun j w => (j,w)) trace placeholders) [] = (.ok (result,w),history)) :
    Ready history w := by
  have checked := initialized_endpoint Ready Returned CompleteProduct.Safe empty_safe ready_safe
    ready_prepare ready_close (Driver.syscallObserved hooks) syscall_closed trace placeholders
    (ready_initial trace.net trace.bare)
  simpa only [run] using checked

/-- The same initialized normal execution supplies both the original result
and a complete ledger on its actual returned World, with no snapshot premise. -/
theorem normal_cut (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (CausalJournal.execute trace placeholders) [] = (.ok result,history)) :
    ∃ w ledger,
      runPrefixOuter (Queues.RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
        (fun j w => (j,w)) trace placeholders) [] = (.ok (result,w),history) ∧
      CompleteConsequences.Cut history ledger [] [] w.wg := by
  have equation := history_correspondence trace placeholders []
  rw [run] at equation
  cases paired : runPrefixOuter (Queues.RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun j w => (j,w)) trace placeholders) [] with
  | mk outcome h =>
    rw [paired] at equation
    cases outcome with
    | error reason => cases equation
    | ok out =>
      rcases out with ⟨value,w⟩
      cases equation
      obtain ⟨ledger,accounted⟩ := (normal_ready trace placeholders paired).1.1
      exact ⟨w,ledger,rfl,CompleteConsequences.accounted accounted⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteRunner
