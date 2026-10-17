import Leanux.Proofs.WG.Progress.BacklogSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Runner Campaign2

/-- Actual acceptance supplies the successful audit of the full Product state.
The output remains the runner's complete JSON result. -/
theorem runnerAudit_of_accepted (trace : Trace) (placeholders : Bool)
    (output : Lean.Json) (acceptedRun : executeTrace trace placeholders = .ok output) :
    ∃ audit, executeTraceWithBoundaries trace placeholders = .ok audit ∧
      audit.output = output ∧
      audit.boundaries.map RunnerBoundary.index = List.range trace.ops.size ∧
      audit.boundaries.length = trace.ops.size ∧
      ∀ cut ∈ audit.boundaries, RunnerBoundaryClean cut := by
  have erased := executeTraceWithBoundaries_erases trace placeholders
  rw [acceptedRun] at erased
  cases run : executeTraceWithBoundaries trace placeholders with
  | error error => simp [run, Except.map] at erased
  | ok audit =>
    have same : audit.output = output := by simpa [run, Except.map] using erased
    exact ⟨audit, rfl, same,
      executeTraceWithBoundaries_facts trace placeholders audit run⟩

/-- Historical name retained for audit: both actual and observed execution now
refuse this trace. There is no accepted final operation boundary or backlog claim. -/
theorem pending_accepted_boundary :
    executeTrace pendingTrace =
      .error (1, .outsideDomain "drivers/net/wireguard/queueing.h:128"
        "work the batch queued outlived the guest's wait (its records would be missing)") ∧
    executeTraceWithBoundaries pendingTrace false =
      .error (1, .outsideDomain "drivers/net/wireguard/queueing.h:128"
        "work the batch queued outlived the guest's wait (its records would be missing)") :=
  ⟨pendingTrace_rejected, pending_audit_backlog⟩

end Leanux.Proofs.WG.Progress
