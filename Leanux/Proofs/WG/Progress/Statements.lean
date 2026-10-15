import Leanux.Proofs.WG.Progress.BatchBacklog
import Leanux.Proofs.WG.Progress.Scheduler
import Leanux.Proofs.WG.Progress.Dispatch

namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.Env

/-- The actual runner accepts this two-operation trace with no receive
dispatch after a batch queues a handshake message. Proved by kernel reduction. -/
theorem original_pending_batch_accepted : accepted = true :=
  pendingTrace_accepted

/-- The same initialized fixture and two original syscalls leave one
handshake queue item and the receive-worker identity pending, although all
records are consumed, no activation is suspended and NET_RX is not raised. -/
theorem original_pending_batch_state :
    backlog = some (1, 1, [1], some 0, 0, false) :=
  pendingTrace_backlog

/-- The resumption probe runs the original activation on a copy, reports success or a hidden mismatch, and propagates every other error. -/
theorem original_resume_probe (a : Activation) (w : World) :
    (Activation.consistent a).run w = probeResult w ((Activation.run a).run w) :=
  consistent_exact a w

/-- A successful probe is exactly a successful original activation run from the probed World; the probe preserves that World. -/
theorem original_resume_probe_success (a : Activation) (w v : World) :
    (Activation.consistent a).run w = .ok (true, v) ↔
      v = w ∧ ∃ out, (Activation.run a).run w = .ok out :=
  consistent_success_iff a w v

/-- A false probe is exactly a hidden-input error from the original activation, with the probed World preserved. -/
theorem original_resume_probe_mismatch (a : Activation) (w v : World) :
    (Activation.consistent a).run w = .ok (false, v) ↔
      v = w ∧ ∃ message, (Activation.run a).run w = .error (.hidden message) :=
  consistent_hidden_iff a w v

/-- An empty worker step ends the iteration immediately without running the after-item callback. -/
theorem original_worker_empty (worker : Worker) (pid : Option Nat)
    (step afterItem : M Bool) (w v : World)
    (empty : step.run w = .ok (false, v)) :
    (workerIter worker pid step afterItem).run w = .ok (.ended, v) :=
  workerIter_empty worker pid step afterItem w v empty

/-- A productive worker step runs its after-item callback exactly once; that callback selects yield or continue and its errors propagate. -/
theorem original_worker_productive (worker : Worker) (pid : Option Nat)
    (step afterItem : M Bool) (w v : World)
    (item : step.run w = .ok (true, v)) :
    (workerIter worker pid step afterItem).run w =
      (afterItem.run v >>= fun out =>
        pure (if out.1 then .yielded else .continued, out.2)) :=
  workerIter_productive worker pid step afterItem w v item

/-- Successful original dispatch is exactly its original selection/detachment
prefix, section-start input read and selected activation run, in that order.
The activation starts at iteration zero and has the dispatched worker identity. -/
theorem original_dispatch_runs_activation (worker : Worker) (initial final : World) :
    (Env.dispatch worker).run initial = .ok (true, final) ↔ DispatchRun worker initial final :=
  dispatch_success_iff worker initial final

/-- With a resident device, a worker with no eligible work returns false and
preserves the entire World, including records. Non-draining worker kinds are
also in this dispatch-specific no-work case. -/
theorem original_dispatch_no_work (worker : Worker) (d : WG.Device) (initial : World)
    (device : initial.k.wg = some d) (empty : NoDispatchWork worker d) :
    (Env.dispatch worker).run initial = .ok (false, initial) :=
  dispatch_no_work worker d initial device empty

/-- An original dispatch returns false exactly when selection found no
activation, at the same final World. A selected activation's failed execution
cannot be converted to false. -/
theorem original_dispatch_false (worker : Worker) (initial final : World) :
    (Env.dispatch worker).run initial = .ok (false, final) ↔
      (dispatchPrefix worker).run initial = .ok (none, final) :=
  dispatch_false_iff worker initial final

end Leanux.Proofs.WG.Progress
