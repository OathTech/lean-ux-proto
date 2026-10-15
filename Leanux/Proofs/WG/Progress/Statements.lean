import Leanux.Proofs.WG.Progress.PlaceholderTurn
import Leanux.Proofs.WG.Progress.RecordedTurn
import Leanux.Proofs.WG.Progress.BatchBacklog
import Leanux.Proofs.WG.Progress.Scheduler
import Leanux.Proofs.WG.Progress.Dispatch
import Leanux.Proofs.WG.Progress.StackResume

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

/-- The original scheduler is exactly its record-budgeted loop over the factored
single-turn body. Its normal return and budget-exhaustion continuation are retained. -/
theorem original_schedule_turns (stack : Option Worker) :
    Env.schedule stack = (do
      let budget ← recordBudget
      let result ← forIn [0:budget] ((none, ()) : Option Unit × Unit)
        (fun _ _ => scheduleTurn stack)
      match result.1 with
      | some ret => pure ret
      | none => budgetExhausted "the scheduler loop") :=
  schedule_source stack

/-- A successful original candidate-filter computation preserves the entire
World and selects exactly the successful activation probes, preserving order
and multiplicity. Other probe errors are not silently rejected. -/
theorem original_candidates_exact (candidates : List Activation) (initial final : World)
    (result : List Activation)
    (run : (candidates.filterM Activation.consistent).run initial = .ok (result, final)) :
    final = initial ∧ result = candidates.filter (probeAccepted · initial) :=
  filter_consistent_result candidates initial final result run

/-- At the original recorded scheduler resumption branch with one candidate
and no worker held on the caller stack, detach the activation and run it.
The equation preserves errors from actual execution after detachment; probe
success alone does not assert success of that execution. -/
theorem original_turn_resumes (initial afterPeek : World) (next : Option Nat)
    (d : WG.Device) (a : Activation) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek =
      .ok ([a], afterPeek)) :
    (scheduleTurn none).run initial =
      ((Activation.run a).run (detached afterPeek a) >>= fun out => pure (turnContinue, out.2)) :=
  turn_resumes_singleton initial afterPeek next d a records peek noStart device noPoll candidates

/-- At the original recorded scheduler resumption branch with no candidate,
return immediately at the post-peek World. This is one turn, not a queue-drain claim. -/
theorem original_turn_no_candidate (stack : Option Worker) (initial afterPeek : World) (next : Option Nat)
    (d : WG.Device) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek =
      .ok ([], afterPeek)) :
    (scheduleTurn stack).run initial = .ok (turnReturn, afterPeek) :=
  turn_no_candidates stack initial afterPeek next d records peek noStart device noPoll candidates

/-- At the original recorded scheduler resumption branch with at least two
candidates, stop outside the modeled domain with the ambiguity message and
the original diagnostic site. No activation is committed by that branch. -/
theorem original_turn_ambiguous (stack : Option Worker) (initial afterPeek : World) (next : Option Nat)
    (d : WG.Device) (a b : Activation) (rest : List Activation) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek =
      .ok (a :: b :: rest, afterPeek)) :
    (scheduleTurn stack).run initial =
      .error (.outsideDomain (match afterPeek.steps.back? with
        | some s => s!"{s.decision.info.file}:{s.decision.info.line}"
        | none => "syscall entry")
        "the records do not determine which suspended worker resumed") :=
  turn_ambiguous stack initial afterPeek next d a b rest records peek noStart device noPoll candidates

/-- With a sole suspended candidate and a caller-stack worker that has work,
the original resumption branch stops with its ambiguity diagnostic. The guard
is read-only and no suspended activation is committed by this branch. -/
theorem original_turn_stack_busy (worker : Worker) (initial afterPeek : World) (next : Option Nat)
    (d : WG.Device) (a : Activation) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek = .ok ([a], afterPeek))
    (busy : (Activation.hasWork { worker }).run afterPeek = .ok (true, afterPeek)) :
    (scheduleTurn (some worker)).run initial = .error (resumptionAmbiguity afterPeek) :=
  turn_stack_busy worker initial afterPeek next d a records peek noStart device noPoll candidates busy

/-- With a sole suspended candidate and an idle caller-stack worker, the
original resumption branch detaches and executes that candidate. The equation
retains failures from actual execution; probe success alone is insufficient. -/
theorem original_turn_stack_idle (worker : Worker) (initial afterPeek : World) (next : Option Nat)
    (d : WG.Device) (a : Activation) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek = .ok ([a], afterPeek))
    (idle : (Activation.hasWork { worker }).run afterPeek = .ok (false, afterPeek)) :
    (scheduleTurn (some worker)).run initial =
      ((Activation.run a).run (detached afterPeek a) >>= fun out => pure (turnContinue, out.2)) :=
  turn_stack_idle worker initial afterPeek next d a records peek noStart device noPoll candidates idle

/-- If the caller-stack work guard fails at the original single-candidate
resumption branch, that exact stop propagates. It is not converted into an
idle-worker result or permission to resume the suspended candidate. -/
theorem original_turn_stack_error (worker : Worker) (initial afterPeek : World) (next : Option Nat)
    (d : WG.Device) (a : Activation) (err : Stop) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (noPoll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = false)
    (candidates : (afterPeek.suspended.filterM Activation.consistent).run afterPeek = .ok ([a], afterPeek))
    (failed : (Activation.hasWork { worker }).run afterPeek = .error err) :
    (scheduleTurn (some worker)).run initial = .error err :=
  turn_stack_error worker initial afterPeek next d a err records peek noStart device noPoll candidates failed

/-- At a recorded worker start, the original scheduler continues exactly
when dispatch actually selects an activation, consumes its start read and
executes it. The initial peek may consume ambient records. -/
theorem original_turn_dispatch_runs (stack : Option Worker) (worker : Worker)
    (initial afterPeek final : World) (next : Option Nat)
    (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (start : next.bind sectionOf = some (worker, true)) :
    (scheduleTurn stack).run initial = .ok (turnContinue, final) ↔ DispatchRun worker afterPeek final :=
  turn_dispatch_continue_iff stack worker initial afterPeek final next records peek start

/-- At a recorded worker start, the original scheduler returns exactly when
the original dispatch prefix finds no activation. This is not a global queue
or pending-work emptiness assertion. -/
theorem original_turn_dispatch_empty (stack : Option Worker) (worker : Worker)
    (initial afterPeek final : World) (next : Option Nat)
    (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (start : next.bind sectionOf = some (worker, true)) :
    (scheduleTurn stack).run initial = .ok (turnReturn, final) ↔
      (dispatchPrefix worker).run afterPeek = .ok (none, final) :=
  turn_dispatch_return_iff stack worker initial afterPeek final next records peek start

/-- A failed original dispatch at a recorded worker start propagates its exact
stop through the scheduler turn; it cannot become a no-work return. -/
theorem original_turn_dispatch_error (stack : Option Worker) (worker : Worker)
    (initial afterPeek : World) (next : Option Nat) (err : Stop)
    (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (start : next.bind sectionOf = some (worker, true))
    (failed : (Leanux.Env.dispatch worker).run afterPeek = .error err) :
    (scheduleTurn stack).run initial = .error err :=
  turn_dispatch_error stack worker initial afterPeek next err records peek start failed

/-- On the original recorded NET_RX branch, a normal turn actually executes
NAPI and the post-poll peek. It returns when that peek still names NET_RX,
leaving the section to its caller; otherwise it continues. No poll-state frame,
queue-drain assertion or productive-record-decrease claim is made. -/
theorem original_turn_napi (stack : Option Worker) (initial afterPeek final : World) (next : Option Nat)
    (d : WG.Device) (result : TurnResult) (records : initial.hidden.isNone = false)
    (peek : peekHiddenSite.run initial = .ok (next, afterPeek))
    (noStart : ∀ worker, next.bind sectionOf ≠ some (worker, true))
    (device : afterPeek.k.wg = some d)
    (poll : (next == some (HiddenSite.sectionStart .netRx).info.id &&
      d.peers.toList.any (·.2.napiScheduled)) = true)
    (run : (scheduleTurn stack).run initial = .ok (result, final)) :
    ∃ afterPoll nextAfter,
      napiSoftirq.run afterPeek = .ok ((), afterPoll) ∧
      peekHiddenSite.run afterPoll = .ok (nextAfter, final) ∧
      result = if nextAfter == some (HiddenSite.sectionStart .netRx).info.id then turnReturn else turnContinue := by
  rw [turn_napi stack initial afterPeek next d records peek noStart device poll] at run
  exact napiTurn_execution afterPeek final result run

/-- In recordless mode with a resident device, the original scheduler returns
unchanged when the receive, decrypt, encrypt and transmit readiness tests are
all empty. It does not inspect suspended activations, NAPI, timers or send work
on this branch, so this is not global work emptiness. -/
theorem original_recordless_turn_empty (stack : Option Worker) (initial : World) (d : WG.Device)
    (records : initial.hidden = none) (device : initial.k.wg = some d)
    (empty : d.handshakeQueue.isEmpty = true ∧ d.decryptQueue.empty = true ∧
      d.encryptQueue.empty = true ∧ d.txWorkQueue.isEmpty = true) :
    (scheduleTurn stack).run initial = .ok (turnReturn, initial) :=
  turn_placeholder_empty stack initial d records device empty

/-- A recordless turn selects in original receive/decrypt/encrypt/transmit
priority and continues normally exactly when original dispatch executes its
activation. Recordless mode alone does not enable placeholders or promise a
successful hidden-input read; this is not a fairness or termination claim. -/
theorem original_recordless_turn_runs (stack : Option Worker) (worker : Worker)
    (initial final : World) (d : WG.Device) (records : initial.hidden = none)
    (device : initial.k.wg = some d) (selected : placeholderSelection d = some worker) :
    (scheduleTurn stack).run initial = .ok (turnContinue, final) ↔ DispatchRun worker initial final := by
  rw [turn_placeholder_dispatch stack worker initial d records device selected]
  exact placeholderDispatch_success_iff worker initial final

/-- A selected recordless dispatch failure propagates its exact stop through
the original scheduler turn. In particular, absent records do not authorize
placeholder execution when the original hidden reader rejects it. -/
theorem original_recordless_turn_error (stack : Option Worker) (worker : Worker)
    (initial : World) (d : WG.Device) (err : Stop) (records : initial.hidden = none)
    (device : initial.k.wg = some d) (selected : placeholderSelection d = some worker)
    (failed : (Leanux.Env.dispatch worker).run initial = .error err) :
    (scheduleTurn stack).run initial = .error err := by
  rw [turn_placeholder_dispatch stack worker initial d records device selected]
  exact placeholderDispatch_error worker initial err failed

end Leanux.Proofs.WG.Progress
