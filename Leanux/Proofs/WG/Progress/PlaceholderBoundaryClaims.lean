import Leanux.Proofs.WG.Progress.PlaceholderBoundarySource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CurrentBoundaryWitness
open Leanux Leanux.Runner
/-- The real initialized placeholder-mode runner accepts this trace. Its actual
audited last cut has no pending identity and satisfies the specified empty-queue,
count and NAPI tests. This is a concrete regression, not an all-mode theorem. -/
theorem placeholder_accepted_drained :
    ∃ audit cut d,
      executeTraceWithBoundaries placeholderBoundaryTrace true = .ok audit ∧
      executeTrace placeholderBoundaryTrace true = .ok audit.output ∧
      audit.boundaries[1]? = some cut ∧
      cut.index = 1 ∧ cut.result = 1 ∧ cut.after.wg.device = some d ∧
      cut.after.ambient.pendingWork = [] ∧
      cut.after.ambient.hidden.isNone = true ∧
      cut.after.ambient.suspended.isEmpty = true ∧ cut.after.wg.netRxRaised = false ∧
      d.handshakeQueue.empty = true ∧ d.handshakeQueue.count = 0 ∧
      d.handshakeQueueLen = 0 ∧ d.decryptQueue.empty = true ∧
      d.encryptQueue.empty = true ∧ d.txWorkQueue.isEmpty = true ∧
      d.sendWorkQueue.isEmpty = true ∧ d.clearWorkQueue.isEmpty = true ∧
      d.peers.toList.any (fun item => item.2.napiScheduled) = false := by
  have checked := placeholder_boundary_drained_check
  unfold placeholderBoundaryDrainedCheck at checked
  cases audited : executeTraceWithBoundaries placeholderBoundaryTrace true with
  | error err => simp only [audited, Bool.false_eq_true] at checked
  | ok audit =>
    simp only [audited] at checked
    cases cutRead : audit.boundaries[1]? with
    | none => simp only [cutRead, Bool.false_eq_true] at checked
    | some cut =>
      simp only [cutRead] at checked
      cases device : cut.after.wg.device with
      | none => simp only [device, Bool.false_eq_true] at checked
      | some d =>
        simp only [device] at checked
        have erased := executeTraceWithBoundaries_erases placeholderBoundaryTrace true
        rw [audited] at erased
        change Except.ok audit.output = executeTrace placeholderBoundaryTrace true at erased
        refine ⟨audit,cut,d,rfl,erased.symm,cutRead,?_⟩
        simp only [Bool.and_eq_true, beq_iff_eq] at checked
        grind only


end Leanux.Proofs.WG.Progress.CurrentBoundaryWitness
