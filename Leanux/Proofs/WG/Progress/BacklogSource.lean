import Leanux.Proofs.WG.Progress.RunnerBoundaryAuditSource
import Leanux.Proofs.WG.Progress.BatchBacklog

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Lean Leanux Leanux.Runner Campaign2

section BacklogSource
set_option maxHeartbeats 800000

/-- Backlog fields of an arbitrary actual full Product observation. -/
def boundaryBacklog (entry : Campaign2.Product.Snapshot) :
    Option (Nat × Nat × List Nat × Option Nat × Nat × Bool) := do
  let d ← entry.wg.device
  return (d.handshakeQueue.count, d.handshakeQueueLen, entry.ambient.pendingWork,
    entry.ambient.hidden.map List.length, entry.ambient.suspended.length, entry.wg.netRxRaised)

/-- Correction of the historical two-call correspondence: the direct fixture
has no runner FIB boot and fails before yielding any final backlog state. -/
theorem pending_loop_runTwo : runTwo =
    .error (.invariant "wg_batch: the route disagrees with the sender source") :=
  pendingTrace_runTwo_rejected

/-- The current runner boots the actual FIB before the first operation. Its
result is the actual boot result with only the boot log reset, not the old fixture. -/
theorem pending_runner_initial : runnerInitial pendingTrace false = (do
    let (_, world) ← ((Net.Fib.bootTables : Leanux.M Unit).run
      {initialWorld with ambient := {initialWorld.ambient with hidden := none}}).mapError
        (fun stop => (0, stop))
    pure {world with ambient := {world.ambient with steps := #[], envCalls := []}}) := by
  simp [runnerInitial, pendingTrace, Trace.net, Trace.stepped, initialWorld]
  have routing : (initialWG true).routing = ({foreignCreator := false} : Net.Routing) := rfl
  simp only [routing]
  split <;> rename_i boot
  all_goals rw [boot]
  all_goals rfl

/-- Correction of the historical accepted-boundary backlog: the actual audited
runner rejects operation 1 at the queued-work boundary and yields no audit. -/
theorem pending_audit_backlog : executeTraceWithBoundaries pendingTrace false =
    .error (1, .outsideDomain "drivers/net/wireguard/queueing.h:128"
      "work the batch queued outlived the guest's wait (its records would be missing)") := by
  have erased := executeTraceWithBoundaries_erases pendingTrace false
  rw [pendingTrace_rejected] at erased
  cases run : executeTraceWithBoundaries pendingTrace false with
  | error error =>
    simp only [run, Except.map] at erased
    exact congrArg Except.error (Except.error.inj erased)
  | ok audit =>
    simp only [run, Except.map] at erased
    cases erased

end BacklogSource


end Leanux.Proofs.WG.Progress
