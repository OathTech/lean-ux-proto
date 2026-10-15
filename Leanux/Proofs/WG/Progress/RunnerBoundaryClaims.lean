import Leanux.Proofs.WG.Progress.BacklogSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Runner Campaign2

/-- Original acceptance supplies the successful audit; it is not a premise
substituted for acceptance. The output is the original complete JSON result. -/
theorem runnerAudit_of_accepted (trace : Trace) (placeholders floodExact : Bool)
    (output : Lean.Json)
    (acceptedRun : executeTrace trace placeholders floodExact = .ok output) :
    ∃ audit, executeTraceWithBoundaries trace placeholders floodExact = .ok audit ∧
      audit.output = output ∧
      audit.boundaries.map RunnerBoundary.index = List.range trace.ops.size ∧
      audit.boundaries.length = trace.ops.size ∧
      ∀ cut ∈ audit.boundaries, RunnerBoundaryClean cut := by
  have erased := executeTraceWithBoundaries_erases trace placeholders floodExact
  rw [acceptedRun] at erased
  cases run : executeTraceWithBoundaries trace placeholders floodExact with
  | error error => simp [run, Except.map] at erased
  | ok audit =>
    have same : audit.output = output := by simpa [run, Except.map] using erased
    exact ⟨audit, rfl, same,
      executeTraceWithBoundaries_facts trace placeholders floodExact audit run⟩

/-- The historical accepted trace's backlog is located at its actual final
operation boundary. No parsed/captured Linux execution is asserted. -/
theorem pending_accepted_boundary :
    ∃ audit first second,
      executeTraceWithBoundaries pendingTrace false false = .ok audit ∧
      executeTrace pendingTrace = .ok audit.output ∧
      audit.boundaries = [first, second] ∧
      first.index = 0 ∧ second.index = 1 ∧
      RunnerBoundaryClean first ∧ RunnerBoundaryClean second ∧
      boundaryBacklog second.after = some (1, 1, [1], some 0, 0, false) := by
  have acceptance := pendingTrace_accepted
  unfold accepted at acceptance
  cases actual : executeTrace pendingTrace with
  | error error => simp [actual] at acceptance
  | ok output =>
    obtain ⟨audit, audited, same, indices, _, clean⟩ :=
      runnerAudit_of_accepted pendingTrace false false output actual
    obtain ⟨first, second, shape, pending⟩ := pending_audit_backlog audit audited
    have ordered : first.index = 0 ∧ second.index = 1 := by
      simpa [shape, pendingTrace, show List.range 2 = [0, 1] from rfl] using indices
    refine ⟨audit, first, second, audited, ?_, shape, ordered.1, ordered.2, ?_, ?_, pending⟩
    · simpa only [same] using actual
    · exact clean first (by simp [shape])
    · exact clean second (by simp [shape])

end Leanux.Proofs.WG.Progress
