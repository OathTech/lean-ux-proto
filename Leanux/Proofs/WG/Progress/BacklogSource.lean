import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource
import Leanux.Proofs.WG.Progress.BatchBacklog

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Progress
open Lean Leanux Leanux.Runner Campaign2

/-- The historical backlog observation, expressed solely over the projection. -/
def boundaryBacklog (entry : Snapshot) :
    Option (Nat × Nat × List Nat × Option Nat × Nat × Bool) := do
  let d ← entry.wg.device
  return (d.handshakeQueue.length, d.handshakeQueueLen, entry.ambient.pendingWork,
    entry.ambient.hidden.map List.length, entry.ambient.suspended.length, entry.wg.netRxRaised)

/-- This is a symbolic threading proof; neither original syscall is re-evaluated. -/
theorem pending_loop_runTwo (final : RunnerAccumulator) (cuts : List RunnerBoundary)
    (run : runnerAuditLoop pendingTrace pendingTrace.ops.toList
      ({initialWorld with hidden := none}, #[], #[], #[], #[], #[]) = .ok (final, cuts)) :
    runTwo = .ok final.1 ∧
    ∃ first second, cuts = [first, second] ∧ second.after = snapshot final.1 := by
  change runnerAuditLoop pendingTrace
    [.wgUp, .wgBatch [.inject 4 32768 cookie64] 100] _ = _ at run
  obtain ⟨ret₁, after₁, next₁, rest₁, op₁, world₁, results₁, tail₁, cuts₁⟩ :=
    runnerAuditLoop_cons_success _ _ _ _ _ _ run
  obtain ⟨ret₂, after₂, next₂, rest₂, op₂, world₂, results₂, tail₂, cuts₂⟩ :=
    runnerAuditLoop_cons_success _ _ _ _ _ _ tail₁
  simp only [runnerAuditLoop, Except.ok.injEq, Prod.mk.injEq] at tail₂
  obtain ⟨rfl, rfl⟩ := tail₂
  obtain ⟨⟨middle₁, call₁, ambient₁⟩, _⟩ := runnerOperation_facts _ _ _ _ _ op₁
  obtain ⟨⟨middle₂, call₂, ambient₂⟩, _⟩ := runnerOperation_facts _ _ _ _ _ op₂
  have call₁' : (syscall .wgUp).run initialWorld = .ok (ret₁, middle₁) := by
    exact call₁
  have entry₂ : runnerEntry pendingTrace next₁ =
      { after₁ with hidden := some batchRecords, netRxRaised := false } := by
    simp [runnerEntry, results₁, world₁, pendingTrace]
  have call₂' : (syscall (.wgBatch [.inject 4 32768 cookie64] 100)).run
      {after₁ with hidden := some batchRecords, netRxRaised := false} = .ok (ret₂, middle₂) := by
    simpa only [toSyscall, entry₂] using call₂
  refine ⟨?_, ?_⟩
  · unfold runTwo
    rw [call₁']
    simp only [Bind.bind, Except.bind]
    rw [ambient₁]
    simp only [Bind.bind, Except.bind]
    rw [call₂']
    simp only [Bind.bind, Except.bind]
    rw [ambient₂]
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure]
    rw [world₂]
  · refine ⟨⟨0, ret₁, snapshot after₁⟩,
      ⟨next₁.2.1.size, ret₂, snapshot after₂⟩, ?_, ?_⟩
    · rw [cuts₁, cuts₂]
      rfl
    · exact congrArg snapshot world₂.symm

/-- The runner's original initialization for the historical trace, before its
first operation installs the recorded inputs. -/
theorem pending_runner_initial : runnerInitial pendingTrace false false =
    .ok {initialWorld with hidden := none} := by
  simp [runnerInitial, pendingTrace, Trace.net, Trace.stepped, initialWorld,
    Pure.pure, Except.pure]

/-- Acceptance supplies all omitted guards before relating the old two-call
fixture to the final actual runner boundary. -/
theorem pending_audit_backlog (audit : RunnerBoundaryAudit)
    (run : executeTraceWithBoundaries pendingTrace false false = .ok audit) :
    ∃ first second, audit.boundaries = [first, second] ∧
      boundaryBacklog second.after = some (1, 1, [1], some 0, 0, false) := by
  unfold executeTraceWithBoundaries at run
  rw [pending_runner_initial] at run
  simp only [Bind.bind, Except.bind] at run
  change (do
    let (final, cuts) ← runnerAuditLoop pendingTrace pendingTrace.ops.toList
      ({initialWorld with hidden := none}, #[], #[], #[], #[], #[])
    let output ← runnerFinish pendingTrace final
    pure (RunnerBoundaryAudit.mk output cuts)) = .ok audit at run
  cases hl : runnerAuditLoop pendingTrace pendingTrace.ops.toList
      ({initialWorld with hidden := none}, #[], #[], #[], #[], #[]) with
  | error error => simp [hl, Bind.bind, Except.bind] at run
  | ok pair =>
    obtain ⟨final, cuts⟩ := pair
    simp only [hl, Bind.bind, Except.bind] at run
    cases hf : runnerFinish pendingTrace final with
    | error error => simp [hf, Bind.bind, Except.bind] at run
    | ok output =>
      simp only [hf, Bind.bind, Except.bind, Pure.pure, Except.pure, Except.ok.injEq] at run
      subst audit
      obtain ⟨two, first, second, shape, finalSnapshot⟩ := pending_loop_runTwo final cuts hl
      refine ⟨first, second, shape, ?_⟩
      rw [finalSnapshot]
      have known := pendingTrace_backlog
      unfold backlog at known
      rw [two] at known
      exact known

end Leanux.Proofs.WG.Progress
