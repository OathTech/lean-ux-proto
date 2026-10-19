import Leanux.Proofs.WG.Progress.ActivationFiniteClaims
import Leanux.Proofs.WG.Progress.SchedulerFiniteClaims
import Leanux.Proofs.WG.Progress.PeerFiniteClaims
import Leanux.Proofs.WG.Progress.AllowedFiniteClaims
import Leanux.Proofs.WG.Progress.CookieFiniteClaims
import Leanux.Proofs.WG.Progress.ReceptionFiniteClaims
import Leanux.Proofs.WG.Progress.InitiationFiniteClaims
import Leanux.Proofs.WG.Progress.ConsumerFiniteClaims
import Leanux.Proofs.WG.Progress.SendBufferFiniteClaims
import Leanux.Proofs.WG.Progress.ResponseSenderFiniteClaims
import Leanux.Proofs.WG.Progress.InitiationCallerFiniteClaims
import Leanux.Proofs.WG.Progress.KeepaliveFiniteClaims
import Leanux.Proofs.WG.Progress.BatchBudgetClaims
import Leanux.Proofs.WG.Progress.SendLoopRecordClaims
import Leanux.Proofs.WG.Progress.TimerBudgetClaims
import Leanux.Proofs.WG.Progress.BatchLoopRecordClaims
import Leanux.Proofs.WG.Progress.TimerTurnRecordClaims
import Leanux.Proofs.WG.Progress.SchedulerBudgetClaims
import Leanux.Proofs.WG.Progress.CommittedRecordClaims
import Leanux.Proofs.WG.Progress.TimerLoopRecordClaims
import Leanux.Proofs.WG.Progress.TimerUnitRecordClaims
import Leanux.Proofs.WG.Progress.SchedulerRecordClaims
import Leanux.Proofs.WG.Progress.DeliverySuffixClaims
import Leanux.Proofs.WG.Progress.TimerCallbackSuffixClaims
import Leanux.Proofs.WG.Progress.TransmitRecordClaims
import Leanux.Proofs.WG.Progress.NapiSuffixClaims
import Leanux.Proofs.WG.Progress.HandshakeSuffixClaims
import Leanux.Proofs.WG.Progress.StackSuffixClaims
import Leanux.Proofs.WG.Progress.SocketSuffixClaims
import Leanux.Proofs.WG.Progress.EncryptSuffixClaims
import Leanux.Proofs.WG.Progress.RoutingIPv4SuffixClaims
import Leanux.Proofs.WG.Progress.StackLeafSuffixClaims
import Leanux.Proofs.WG.Progress.ConsumeSuffixClaims
import Leanux.Proofs.WG.Progress.ReceiveTerminalClaims
import Leanux.Proofs.WG.Progress.ClearWorkerRecordClaims
import Leanux.Proofs.WG.Progress.PipeReadClaims
import Leanux.Proofs.WG.Progress.PipeWriteOuterClaims
import Leanux.Proofs.WG.Progress.StagingSuffixClaims
import Leanux.Proofs.WG.Progress.TimerSuffixClaims
import Leanux.Proofs.WG.Progress.RecordedPending
import Leanux.Proofs.WG.Progress.PipeWriteClaims
import Leanux.Proofs.WG.Progress.ReceiveCompletionSuffixSource
import Leanux.Proofs.WG.Progress.PipeFreeClaims
import Leanux.Proofs.WG.Progress.CommittedInitializedReceiptClaims
import Leanux.Proofs.WG.Progress.CommittedSyscallClaims
import Leanux.Proofs.WG.Progress.CommittedInitializedClaims
import Leanux.Proofs.WG.Progress.ReleaseSuffixClaims
import Leanux.Proofs.WG.Progress.DecryptStepSuffixSource
import Leanux.Proofs.WG.Progress.CutJitterSuffixClaims
import Leanux.Proofs.WG.Progress.DecryptSuffixClaims
import Leanux.Proofs.WG.Progress.CommittedTrafficClaims
import Leanux.Proofs.WG.Progress.PipeRoundupClaims
import Leanux.Proofs.WG.Progress.ActivationRecordClaims
import Leanux.Proofs.WG.Progress.CommittedDeferredClaims
import Leanux.Proofs.WG.Progress.CurveFiniteClaims
import Leanux.Proofs.WG.Progress.RecordSuffixClaims
import Leanux.Proofs.WG.Progress.CommittedRunClaims
import Leanux.Proofs.WG.Progress.DecryptOccupancyClaims
import Leanux.Proofs.WG.Progress.ActivationExitClaims
import Leanux.Proofs.WG.Progress.PowEvaluationSource
import Leanux.Proofs.WG.Progress.AllocationProgressClaims
import Leanux.Proofs.WG.Progress.PlaceholderBoundaryClaims
import Leanux.Proofs.WG.Progress.RunnerIdleOperationSource
import Leanux.Proofs.WG.Progress.SendCompletionClaims
import Leanux.Proofs.WG.Progress.RunnerAdvanceSource
import Leanux.Proofs.WG.Progress.AdvanceWaitClaims
import Leanux.Proofs.WG.Progress.TimerWaitClaims
import Leanux.Proofs.WG.Progress.TimerCompletionClaims
import Leanux.Proofs.WG.Progress.BatchDrainClaims
import Leanux.Proofs.WG.Progress.CookieScheduleClaims
import Leanux.Proofs.WG.Progress.SourceClaims
import Leanux.Proofs.WG.Progress.CookieActivationClaims
import Leanux.Proofs.WG.Progress.ObservationBridge
import Leanux.Proofs.WG.Progress.CutClaims
import Leanux.Proofs.WG.Progress.FlushQueueClaims
import Leanux.Proofs.WG.Progress.PowSource
import Leanux.Proofs.WG.Progress.DrainClaims
import Leanux.Proofs.WG.Progress.PollBoundClaims
import Leanux.Proofs.WG.Progress.RunnerBoundaryClaims
import Leanux.Proofs.WG.Progress.IndexProgressClaims
import Leanux.Proofs.WG.Progress.JitterProgressClaims

/-! Projected H5 contracts. Inspection adapters report the exact original
outcomes from the same concrete entry; their totality is not a claim that the
inspected operation succeeds. Generic callback laws are explicitly generic. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Campaign2.Product

/-- The historical trace is rejected at the current batch-completion boundary. -/
theorem original_pending_batch_accepted : accepted = false :=
  SourceClaims.original_pending_batch_accepted


/-- The old direct-call fixture omits current FIB initialization and yields no backlog. -/
theorem original_pending_batch_state : backlog = none :=
  SourceClaims.original_pending_batch_state


/-- Every accepted original trace supplies exactly its ordered operation
boundaries after ambient stripping and the original three completion guards.
These guards say nothing about pending workers or scheduled NAPI. -/
theorem original_accepted_operation_boundaries (trace : Runner.Trace)
    (placeholders : Bool) (output : Lean.Json)
    (acceptedRun : Runner.executeTrace trace placeholders = .ok output) :
    ∃ audit, executeTraceWithBoundaries trace placeholders = .ok audit ∧
      audit.output = output ∧
      audit.boundaries.map RunnerBoundary.index = List.range trace.ops.size ∧
      audit.boundaries.length = trace.ops.size ∧
      ∀ cut ∈ audit.boundaries, RunnerBoundaryClean cut :=
  runnerAudit_of_accepted trace placeholders output acceptedRun

/-- Actual execution and its boundary audit retain the same exact batch refusal.
There is no accepted final-state witness. -/
theorem original_pending_batch_boundary :
    Runner.executeTrace pendingTrace =
      .error (1, .outsideDomain "drivers/net/wireguard/queueing.h:128"
        "work the batch queued outlived the guest's wait (its records would be missing)") ∧
    executeTraceWithBoundaries pendingTrace false =
      .error (1, .outsideDomain "drivers/net/wireguard/queueing.h:128"
        "work the batch queued outlived the guest's wait (its records would be missing)") :=
  pending_accepted_boundary


/-- The original probe reports successful execution or hidden mismatch on its
entry snapshot, and propagates every other exact error. -/
theorem original_resume_probe (a : Activation) :
    Returns (probeObservation a) (fun _ => True)
      (fun observation entry => observation.probe = probeOutcome entry observation.activation) := by
  intro w _
  refine ⟨_, w, rfl, ?_⟩
  change observeResult ((Activation.consistent a).run w) =
    probeOutcome (snapshot w) (observeResult ((Activation.run a).run w))
  rw [consistent_exact]
  cases h : (Activation.run a).run w with
  | ok pair => rfl
  | error err => cases err <;> rfl

/-- Success is exactly an actual successful activation from that same entry;
the probe's final projection equals its entry projection. -/
theorem original_resume_probe_success (a : Activation) :
    Returns (probeObservation a) (fun _ => True)
      (fun observation entry => ∀ final,
        observation.probe = .ok (true, final) ↔
          final = entry ∧ ∃ out, observation.activation = .ok out) := by
  intro w _
  refine ⟨_, w, rfl, ?_⟩
  intro final
  change observeResult ((Activation.consistent a).run w) = .ok (true, final) ↔ _
  rw [consistent_exact]
  cases h : (Activation.run a).run w with
  | ok pair => simp [probeResult, observeResult, Except.map, eq_comm]
  | error err => cases err <;> simp [probeResult, observeResult, Except.map]

/-- False means exactly a hidden-input error from that same original activation;
the inspected entry is preserved. -/
theorem original_resume_probe_mismatch (a : Activation) :
    Returns (probeObservation a) (fun _ => True)
      (fun observation entry => ∀ final,
        observation.probe = .ok (false, final) ↔
          final = entry ∧ ∃ message, observation.activation = .error (.hidden message)) := by
  intro w _
  refine ⟨_, w, rfl, ?_⟩
  intro final
  change observeResult ((Activation.consistent a).run w) = .ok (false, final) ↔ _
  rw [consistent_exact]
  cases h : (Activation.run a).run w with
  | ok pair => simp [probeResult, observeResult, Except.map]
  | error err => cases err <;> simp [probeResult, observeResult, Except.map, eq_comm]

/-- Generic control law, instantiated to the complete original worker by
workerIter_control. Arbitrary callbacks have no assumed WG locality. -/
theorem original_worker_empty {σ ε : Type}
    (step afterItem : StateT σ (Except ε) Bool) (initial after : σ)
    (empty : step.run initial = .ok (false, after)) :
    (Control.iterate step afterItem).run initial = .ok (.ended, after) :=
  Control.empty step afterItem initial after empty

/-- The productive generic control law retains one actual callback execution
and its exact errors; workerIter_control gives the original worker instance. -/
theorem original_worker_productive {σ ε : Type}
    (step afterItem : StateT σ (Except ε) Bool) (initial after : σ)
    (item : step.run initial = .ok (true, after)) :
    (Control.iterate step afterItem).run initial =
      (afterItem.run after >>= fun out => pure (if out.1 then .yielded else .continued, out.2)) :=
  Control.productive step afterItem initial after item

/-- Exact original dispatch outcomes agree with the decorated original
prefix/start/activation sequence. The trace retains actual selection and start
observations; erasure preserves all success and error outcomes. -/
theorem original_dispatch_runs_activation (worker : Worker) :
    Returns (dispatchObservation worker) (fun _ => True)
      (fun observation _ => observation.actual = mapOutcome Option.isSome observation.traced ∧
        ∀ final, observation.actual = .ok (true, final) ↔
          ∃ trace, observation.traced = .ok (some trace, final)) := by
  intro w _
  exact ⟨_, w, rfl, dispatch_observation_exact worker w, traced_success_iff worker w⟩

/-- Dispatch-specific no-work returns false and preserves every retained field,
including records. The concrete whole-state frame remains in the source proof. -/
theorem original_dispatch_no_work (worker : Worker) (d : Device) (entry : Snapshot)
    (empty : NoDispatchWork worker d) :
    Returns (Env.dispatch worker) (fun s => s = entry ∧ s.wg.device = some d)
      (fun result final => result = false ∧ final = entry) := by
  intro w pre
  exact ⟨false, w, dispatch_no_work worker d w pre.2 empty, rfl, pre.1⟩

/-- False is equivalent to the original selection prefix finding no activation,
at the same projected final state. Actual selected execution cannot become false. -/
theorem original_dispatch_false (worker : Worker) :
    Returns (dispatchObservation worker) (fun _ => True)
      (fun observation _ => ∀ final,
        observation.actual = .ok (false, final) ↔ observation.selection = .ok (none, final)) := by
  intro w _
  refine ⟨_, w, rfl, ?_⟩
  intro final
  exact observe_success_iff _ _ false none final (dispatch_false_iff worker w)

/-- Original scheduler and factored loop agree on every concrete realization,
including normal return and the exact budget-exhaustion continuation. -/
theorem original_schedule_turns (stack : Option Worker) :
    AgreesOn (fun _ => True) (Env.schedule stack) (do
      let budget ← recordBudget
      let result ← forIn [0:budget] ((none, ()) : Option Unit × Unit)
        (fun _ _ => scheduleTurn stack)
      match result.1 with
      | some ret => pure ret
      | none => budgetExhausted "the scheduler loop") := by
  intro w _
  rw [schedule_source]
  rfl

/-- Successful original candidate filtering preserves the entry projection and
selects precisely successful same-entry activation probes, in order and with
multiplicity. Failure is not silently reclassified as rejection. -/
theorem original_candidates_exact (candidates : List Activation) :
    Returns (candidateObservation candidates) (fun _ => True)
      (fun observation entry => ∀ result final,
        observation.actual = .ok (result, final) →
          final = entry ∧ result = candidates.filter (fun a => successful (observation.probes a))) := by
  intro w _
  refine ⟨_, w, rfl, ?_⟩
  intro result final run
  change observeResult ((candidates.filterM Activation.consistent).run w) = .ok (result, final) at run
  cases hr : (candidates.filterM Activation.consistent).run w with
  | error e => rw [hr] at run; cases run
  | ok pair =>
    obtain ⟨value, v⟩ := pair
    obtain ⟨same, values⟩ := filter_consistent_result candidates w v value hr
    subst v
    rw [hr] at run
    change Except.ok (value, snapshot w) = Except.ok (result, final) at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    refine ⟨rfl, ?_⟩
    rw [values]
    congr 1
    funext a
    change probeAccepted a w = successful (observeResult ((Activation.run a).run w))
    unfold probeAccepted
    cases h : (Activation.run a).run w <;> rfl

/-- At a successful recorded peek selecting the singleton resumption branch,
run the original detach-and-activation computation. Actual execution errors are
retained; probe success is not a success claim about committed execution. -/
theorem original_turn_resumes (d : Device) (a : Activation) :
    Returns (turnObservation none) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        ResumeBranch after d → after.candidates = .ok ([a], after.state) →
          observation.actual = after.resumed a) := by
  apply turn_contract none _ (fun actual after =>
    ResumeBranch after d → after.candidates = .ok ([a], after.state) →
          actual = after.resumed a)
  intro initial next after records peek branch candidates
  obtain ⟨noStart, device, noPoll⟩ := branch
  have selected := filter_observation candidates
  have same := turn_resumes_singleton initial after next d a records peek noStart device noPoll selected
  change observeResult ((scheduleTurn none).run initial) =
    observeResult ((resumeCandidates none [a]).run after)
  rw [same, resumeCandidates_singleton]

/-- No candidate returns at the actual post-peek projection. This is one turn,
not global queue emptiness or a full scheduler termination claim. -/
theorem original_turn_no_candidate (stack : Option Worker) (d : Device) :
    Returns (turnObservation stack) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        ResumeBranch after d → after.candidates = .ok ([], after.state) →
          observation.actual = .ok (turnReturn, after.state)) := by
  apply turn_contract stack _ (fun actual after =>
    ResumeBranch after d → after.candidates = .ok ([], after.state) →
          actual = .ok (turnReturn, after.state))
  intro initial next after records peek branch candidates
  obtain ⟨noStart, device, noPoll⟩ := branch
  have same := turn_no_candidates stack initial after next d records peek noStart device noPoll
    (filter_observation candidates)
  change observeResult ((scheduleTurn stack).run initial) = .ok (turnReturn, snapshot after)
  rw [same]
  rfl

/-- Multiple actual successful candidates produce the original exact ambiguity
stop and diagnostic site, with no committed activation on that branch. -/
theorem original_turn_ambiguous (stack : Option Worker) (d : Device)
    (a b : Activation) (rest : List Activation) :
    Returns (turnObservation stack) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        ResumeBranch after d → after.candidates = .ok (a :: b :: rest, after.state) →
          observation.actual = .error (ambiguity after.state)) := by
  apply turn_contract stack _ (fun actual after =>
    ResumeBranch after d → after.candidates = .ok (a :: b :: rest, after.state) →
          actual = .error (ambiguity after.state))
  intro initial next after records peek branch candidates
  obtain ⟨noStart, device, noPoll⟩ := branch
  have same := turn_ambiguous stack initial after next d a b rest records peek noStart device noPoll
    (filter_observation candidates)
  change observeResult ((scheduleTurn stack).run initial) = .error (ambiguity (snapshot after))
  rw [same]
  rfl

/-- A busy actual caller-stack guard rejects singleton resumption with its
original ambiguity stop. The guard frame is proved separately. -/
theorem original_turn_stack_busy (worker : Worker) (d : Device) (a : Activation) :
    Returns (turnObservation (some worker)) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        ResumeBranch after d → after.candidates = .ok ([a], after.state) →
        after.guard worker = .ok (true, after.state) →
          observation.actual = .error (ambiguity after.state)) := by
  apply turn_contract (some worker) _ (fun actual after =>
    ResumeBranch after d → after.candidates = .ok ([a], after.state) →
        after.guard worker = .ok (true, after.state) →
          actual = .error (ambiguity after.state))
  intro initial next after records peek branch candidates busy
  obtain ⟨noStart, device, noPoll⟩ := branch
  have same := turn_stack_busy worker initial after next d a records peek noStart device noPoll
    (filter_observation candidates) (guard_observation busy)
  change observeResult ((scheduleTurn (some worker)).run initial) = .error (ambiguity (snapshot after))
  rw [same]
  rfl

/-- An idle actual caller-stack guard permits the same detach-and-run
computation as the no-stack case, retaining its exact execution errors. -/
theorem original_turn_stack_idle (worker : Worker) (d : Device) (a : Activation) :
    Returns (turnObservation (some worker)) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        ResumeBranch after d → after.candidates = .ok ([a], after.state) →
        after.guard worker = .ok (false, after.state) →
          observation.actual = after.resumed a) := by
  apply turn_contract (some worker) _ (fun actual after =>
    ResumeBranch after d → after.candidates = .ok ([a], after.state) →
        after.guard worker = .ok (false, after.state) →
          actual = after.resumed a)
  intro initial next after records peek branch candidates idle
  obtain ⟨noStart, device, noPoll⟩ := branch
  have same := turn_stack_idle worker initial after next d a records peek noStart device noPoll
    (filter_observation candidates) (guard_observation idle)
  change observeResult ((scheduleTurn (some worker)).run initial) =
    observeResult ((resumeCandidates none [a]).run after)
  rw [same, resumeCandidates_singleton]

/-- Every exact caller-stack guard stop propagates; failure does not count as
idle or authorize committing the candidate. -/
theorem original_turn_stack_error (worker : Worker) (d : Device) (a : Activation) (err : Stop) :
    Returns (turnObservation (some worker)) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        ResumeBranch after d → after.candidates = .ok ([a], after.state) →
        after.guard worker = .error err → observation.actual = .error err) := by
  apply turn_contract (some worker) _ (fun actual after =>
    ResumeBranch after d → after.candidates = .ok ([a], after.state) →
        after.guard worker = .error err → actual = .error err)
  intro initial next after records peek branch candidates failed
  obtain ⟨noStart, device, noPoll⟩ := branch
  have failure := (observe_error_iff _ err).mp failed
  have same := turn_stack_error worker initial after next d a err records peek noStart device noPoll
    (filter_observation candidates) failure
  change observeResult ((scheduleTurn (some worker)).run initial) = .error err
  rw [same]
  rfl

/-- At an actual recorded start, continuation is equivalent to a successful
original selected-prefix/start/activation sequence from the post-peek state.
The witness is the decorated same execution, not independent projected runs. -/
theorem original_turn_dispatch_runs (stack : Option Worker) (worker : Worker) :
    Returns (turnObservation stack) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        after.next.bind sectionOf = some (worker, true) → ∀ final,
          observation.actual = .ok (turnContinue, final) ↔
            ∃ trace, (after.dispatch worker).traced = .ok (some trace, final)) := by
  apply turn_contract stack _ (fun actual after =>
    after.next.bind sectionOf = some (worker, true) → ∀ final,
          actual = .ok (turnContinue, final) ↔
            ∃ trace, (after.dispatch worker).traced = .ok (some trace, final))
  intro initial next after records peek start final
  have concrete : ∀ final,
      (scheduleTurn stack).run initial = .ok (turnContinue, final) ↔
        (Env.dispatch worker).run after = .ok (true, final) := by
    intro final
    rw [turn_dispatch_continue_iff stack worker initial after final next records peek start,
      dispatch_success_iff]
  exact (observe_success_iff _ _ turnContinue true final concrete).trans
    (traced_success_iff worker after final)

/-- At that same actual recorded start, returning is equivalent to the original
prefix selecting no activation, at the same projected final state. -/
theorem original_turn_dispatch_empty (stack : Option Worker) (worker : Worker) :
    Returns (turnObservation stack) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        after.next.bind sectionOf = some (worker, true) → ∀ final,
          observation.actual = .ok (turnReturn, final) ↔
            (after.dispatch worker).selection = .ok (none, final)) := by
  apply turn_contract stack _ (fun actual after =>
    after.next.bind sectionOf = some (worker, true) → ∀ final,
          actual = .ok (turnReturn, final) ↔
            (after.dispatch worker).selection = .ok (none, final))
  intro initial next after records peek start final
  exact observe_success_iff _ _ turnReturn none final
    (fun final => turn_dispatch_return_iff stack worker initial after final next records peek start)

/-- The actual recorded dispatch's exact stop is propagated by the turn. -/
theorem original_turn_dispatch_error (stack : Option Worker) (worker : Worker) (err : Stop) :
    Returns (turnObservation stack) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        after.next.bind sectionOf = some (worker, true) →
        (after.dispatch worker).actual = .error err → observation.actual = .error err) := by
  apply turn_contract stack _ (fun actual after =>
    after.next.bind sectionOf = some (worker, true) →
        (after.dispatch worker).actual = .error err → actual = .error err)
  intro initial next after records peek start failed
  have same := turn_dispatch_error stack worker initial after next err records peek start
    ((observe_error_iff _ err).mp failed)
  change observeResult ((scheduleTurn stack).run initial) = .error err
  rw [same]
  rfl

/-- The NET_RX branch agrees exactly with original NAPI followed by its actual
post-poll peek. The decoration retains the post-poll projection and peek value;
no frame or queue-drain assertion is imposed on NAPI. -/
theorem original_turn_napi (stack : Option Worker) (d : Device) :
    Returns (turnObservation stack) (fun s => s.ambient.hidden.isNone = false)
      (fun observation _ => ∀ after, observation.afterPeek = .ok after →
        NoStart after → after.state.wg.device = some d → PollReady after d = true →
          observation.actual = mapOutcome napiResult after.napi) := by
  apply turn_contract stack _ (fun actual after =>
    NoStart after → after.state.wg.device = some d → PollReady after d = true →
          actual = mapOutcome napiResult after.napi)
  intro initial next after records peek noStart device poll
  change observeResult ((scheduleTurn stack).run initial) =
    mapOutcome napiResult (observeResult (tracedNapi.run after))
  rw [turn_napi stack initial after next d records peek noStart device poll,
    tracedNapi_erase, StateT.run_bind]
  exact observe_map napiResult (tracedNapi.run after)

/-- Recordless local no-work returns and preserves the entire retained snapshot.
Suspended activations, timers and NAPI are not part of this branch's tests. -/
theorem original_recordless_turn_empty (stack : Option Worker) (d : Device) (entry : Snapshot)
    (empty : d.handshakeQueue.empty = true ∧ d.decryptQueue.empty = true ∧
      d.encryptQueue.empty = true ∧ d.txWorkQueue.isEmpty = true) :
    Returns (scheduleTurn stack)
      (fun s => s = entry ∧ s.ambient.hidden = none ∧ s.wg.device = some d)
      (fun result final => result = turnReturn ∧ final = entry) := by
  intro w pre
  exact ⟨turnReturn, w, turn_placeholder_empty stack w d pre.2.1 pre.2.2 empty, rfl, pre.1⟩

/-- Original recordless priority selects a worker; continuation is equivalent
to its actual decorated prefix/start/activation execution at that same entry.
Recordless mode alone promises neither placeholders nor execution success. -/
theorem original_recordless_turn_runs (stack : Option Worker) (worker : Worker)
    (d : Device) (selected : placeholderSelection d = some worker) :
    Returns (recordlessObservation stack worker)
      (fun s => s.ambient.hidden = none ∧ s.wg.device = some d)
      (fun observation _ => ∀ final,
        observation.1 = .ok (turnContinue, final) ↔
          ∃ trace, observation.2.traced = .ok (some trace, final)) := by
  intro w pre
  refine ⟨_, w, rfl, ?_⟩
  intro final
  have concrete : ∀ final,
      (scheduleTurn stack).run w = .ok (turnContinue, final) ↔
        (Env.dispatch worker).run w = .ok (true, final) := by
    intro final
    rw [SourceClaims.original_recordless_turn_runs stack worker w final d pre.1 pre.2 selected,
      dispatch_success_iff]
  exact (observe_success_iff _ _ turnContinue true final concrete).trans
    (traced_success_iff worker w final)

/-- Recordless selected dispatch failures retain the original exact stop,
including the hidden reader's rejection when placeholders are not enabled. -/
theorem original_recordless_turn_error (stack : Option Worker) (worker : Worker)
    (d : Device) (err : Stop) (selected : placeholderSelection d = some worker) :
    Returns (recordlessObservation stack worker)
      (fun s => s.ambient.hidden = none ∧ s.wg.device = some d)
      (fun observation _ => observation.2.actual = .error err → observation.1 = .error err) := by
  intro w pre
  refine ⟨_, w, rfl, ?_⟩
  intro failed
  have same := SourceClaims.original_recordless_turn_error stack worker w d err pre.1 pre.2 selected
    ((observe_error_iff _ err).mp failed)
  change observeResult ((scheduleTurn stack).run w) = .error err
  rw [same]
  rfl

/-- The original recorded cut cannot exhaust its record-derived budget.
It either returns a suffix at an empty/non-cut boundary, with every reported
site selected and costing at least one input record, or propagates the actual
below-cut allocation error with its original location and message. Passive
records cost input but are not reported. No exact reported-site order is claimed. -/
theorem original_cut_records_outcome (sites : List HiddenSite) (records : List HiddenRecord) :
    Campaign2.Observes (skipCutSites sites) (fun entry => entry.ambient.hidden = some records)
      (CutOutcome sites records) :=
  source_cut_outcome sites records

/-- With successful allocation bytes in the selected non-passive prefix,
the original cut returns for every concrete realization of this record stream.
Records after its first stopping boundary need no allocation premise. Empty
allocation payloads have the original successful default byte; this operation
does not check payload lengths. The result has the suffix and consumption bound. -/
theorem original_cut_records_returns (sites : List HiddenSite) (records : List HiddenRecord)
    (accepted : CutAccepted sites records) :
    Campaign2.Returns (skipCutSites sites) (fun entry => entry.ambient.hidden = some records)
      (fun taken final => ∃ rest, final.ambient.hidden = some rest ∧ CutProgress sites records taken rest) :=
  source_cut_returns sites records accepted

/-- On normal return, the original send flush erases the first matching occurrence of pid, if
present, from its entry send queue and preserves the clear queue, even if peer release deletes
pid. If pid was queued, the total queued-work count decreases by exactly one.
No successful completion, queue-selection policy or whole-drain bound is asserted. -/
theorem original_flushed_send_queue (pid : PeerId) (d : Device) :
    Campaign2.Ensures (runFlushedSendWork pid) (fun entry => entry.wg.device = some d)
      (fun _ final => flushQueues final = some (flushedSendQueues pid d) ∧
        (pid ∈ d.sendWorkQueue →
          flushQueueCount (flushedSendQueues pid d) + 1 =
            flushQueueCount (TimerDiscipline.workQueues d))) :=
  source_flushed_send_queue pid d


/-- On normal return, the original clear flush erases the first matching occurrence of pid, if
present, from its entry clear queue and preserves the send queue, including final peer release.
Membership in the entry clear queue gives an exact decrease of one in total work;
duplicates are allowed. This does not promise successful completion or a drain bound. -/
theorem original_flushed_clear_queue (pid : PeerId) (d : Device) :
    Campaign2.Ensures (runFlushedClearWork pid) (fun entry => entry.wg.device = some d)
      (fun _ final => flushQueues final = some (flushedClearQueues pid d) ∧
        (pid ∈ d.clearWorkQueue →
          flushQueueCount (flushedClearQueues pid d) + 1 =
            flushQueueCount (TimerDiscipline.workQueues d))) :=
  source_flushed_clear_queue pid d


/-- The original pure modular-exponentiation loop agrees with a finite,
non-exhausted evaluation of its exact accumulator steps whenever the initial
exponent is smaller than the fuel. Choosing fuel `e + 1` works for every input.
Zero exponent and zero modulus retain the original semantics. This is a local
arithmetic-loop contract, not a complete runner or cryptographic correctness claim. -/
theorem original_pow_mod_finite (b e modulus fuel : Nat) (enough : e < fuel) :
    ∃ final, powEval modulus fuel (1, b % modulus, e) = some final ∧
      final.2.2 = 0 ∧ originalPowMod b e modulus = final.1 :=
  powMod_finite_with_fuel b e modulus fuel enough

/-- The original 4096-turn drain has this exact phase audit: erasing the
inspection datum gives inspection of the original outcome, including every error.
With fewer than 4096 queued items, its own budget cannot be the failure origin
and there are at most initial-count-plus-one loop turns begun. Selection and
worker failures remain possible; their origin comes from the actual failing call,
not its error text. Normal completion is at empty queues or the requested clear.
Inspection itself keeps entry state; the drain's final state is inside its datum.
No successful drain, failed-worker state, or global runner termination is promised. -/
theorem original_drain_bounded (upTo : Option PeerId) :
    ((do let outcome ← Product.observedDrain upTo; pure (Product.eraseDrainOutcome outcome)) =
      inspect (liftWG (drainHandshakeSendWq upTo))) ∧
    (∀ d : Device, flushQueueCount (TimerDiscipline.workQueues d) < 4096 →
      Returns (Product.observedDrain upTo) (fun entry => entry.wg.device = some d)
        (fun outcome _ => Product.DrainBounded upTo
          (flushQueueCount (TimerDiscipline.workQueues d)) outcome)) :=
  ⟨Product.observedDrain_source upTo, fun d enough => Product.source_drain_bounded upTo d enough⟩


/-- With no requested early-clear boundary, every normal original drain return
has both queues empty. The static bound excludes own-budget exhaustion, but
does not exclude a selector or worker failure and does not assert successful return. -/
theorem original_drain_to_empty (d : Device)
    (enough : flushQueueCount (TimerDiscipline.workQueues d) < 4096) :
    Ensures (liftWG (drainHandshakeSendWq none)) (fun entry => entry.wg.device = some d)
      (fun _ final => flushQueues final.toSnapshot = some ([], [])) :=
  Product.source_drain_to_empty d enough


/-- The original rxPoll has this exact phase audit, preserving callback errors
and the historical state before completion. For budget ≤ MAX_QUEUED_PACKETS+1,
every returned loop prefix reaches a queue-test stop or the requested budget;
the poll's own loop-exhaustion guard is therefore false at that actual cut.
A queue-test stop includes an uncrypted head, not only an empty queue. The
count measures cleanup-completed iterations, not callback or internal steps.
Zero budget takes the original early return; normal positive-budget completion
returns less than budget. Actual prefix and completion failures remain possible,
including the unsupported repoll and same-text failures inside callbacks.
Inspection keeps its entry state and does not promise poll/callback completion,
physical queue depletion, or global scheduler progress. -/
theorem original_poll_loop_bound (pid : PeerId) (budget : Nat)
    (toStack : List (List UInt8) → M Unit) :
    ((do let audit ← observedPollBound pid budget toStack
         pure (erasePollBoundAudit audit)) = inspect (WG.rxPoll pid budget toStack)) ∧
    (budget ≤ MAX_QUEUED_PACKETS + 1 →
      Returns (observedPollBound pid budget toStack) (fun _ => True)
        (fun audit _ => PollBoundFacts budget audit)) :=
  ⟨observedPollBound_source pid budget toStack, source_poll_bound pid budget toStack⟩


/-- Exact original insertion over any finite supplied record list. Passive
records are skipped without validating their payloads; malformed/missing draws
retain the original hidden-input error. Search is over the table after removing
this owner's old rows. Success records the exact inserted table and unused
suffix. No owner-residency or table-uniqueness premise is required. -/
theorem original_index_record_outcome (owner : IndexOwner) (d : Device) (records : List HiddenRecord) :
    Campaign2.Observes (liftIndex (indexInsert owner))
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records)
      (fun _ outcome =>
        match resolveIndexSearch (Index.removeOwner owner d.indexTable) records with
        | .error error => outcome = .error error
        | .ok (index, rest) => ∃ final,
          outcome = .ok (index, final) ∧
          final.wg.device = some {d with indexTable :=
            {index, owner} :: Index.removeOwner owner d.indexTable} ∧
          final.ambient.hidden = some rest) :=
  index_record_outcome owner d records

/-- The record-derived budget suffices for arbitrary supplied records, including
ambient records and malformed input. Every outcome is either an explicit hidden
input error or a successful fresh index with a strictly shorter suffix; neither
this loop's budget-exhaustion nor stolen-index stop is possible. This excludes
recordless placeholder/domain-filter execution and makes no scheduler-progress
or table-wide uniqueness claim. -/
theorem original_index_record_progress (owner : IndexOwner) (d : Device) (records : List HiddenRecord) :
    Campaign2.Observes (liftIndex (indexInsert owner))
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records)
      (fun _ outcome =>
        (∃ message, outcome = .error (.hidden message)) ∨
        ∃ index rest final, outcome = .ok (index, final) ∧
          (Index.removeOwner owner d.indexTable).any (·.index == index) = false ∧
          rest.IsSuffix records ∧ rest.length < records.length ∧
          final.wg.device = some {d with indexTable :=
            {index, owner} :: Index.removeOwner owner d.indexTable} ∧
          final.ambient.hidden = some rest) :=
  index_record_progress owner d records

/-- Exact total outcome of either original timer jitter site over arbitrary
finite supplied records, including passive records and malformed input. Success
preserves the entire projected state except the unused record suffix. -/
theorem original_jitter_record_outcome (site : TimerDiscipline.JitterSite) (records : List HiddenRecord) :
    Campaign2.Product.Observes (liftWG (jitterBelowRekeyTimeout site.hiddenSite))
      (fun s => s.ambient.hidden = some records)
      (fun entry outcome => outcome =
        match resolveJitterSearch site records with
        | .error error => .error error
        | .ok (jitter, rest) => .ok (jitter,
            {entry with ambient := {entry.ambient with hidden := some rest}})) :=
  jitter_record_outcome site records

/-- The original record-derived jitter budget suffices: an explicit hidden-input
error or a jitter below HZ / 3 with strictly fewer records. This excludes
recordless execution and makes no distribution or scheduler-progress claim. -/
theorem original_jitter_record_progress (site : TimerDiscipline.JitterSite) (records : List HiddenRecord) :
    Campaign2.Product.Observes (liftWG (jitterBelowRekeyTimeout site.hiddenSite))
      (fun s => s.ambient.hidden = some records)
      (fun entry outcome =>
        (∃ message, outcome = .error (.hidden message)) ∨
        ∃ jitter rest, outcome = .ok (jitter,
            {entry with ambient := {entry.ambient with hidden := some rest}}) ∧
          jitter < HZ / 3 ∧ rest.IsSuffix records ∧ rest.length < records.length) :=
  jitter_record_progress site records

/-- The original entry domain determines exact bounded hybrid execution,
including receive, record and occupancy-exhaustion failures. It does not establish
drain adequacy for arbitrary physical ring metadata. -/
theorem original_cookie_activation_outcome (a : Activation) (d : Device) (records : List HiddenRecord)
    (receive : a.worker = .receiveWorker) (table : d.indexTable = []) (cookies : CookieOnly d) :
    Campaign2.Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records)
      (Activation.run a) (cookieHybridRun a d.handshakeQueue.count) :=
  cookieActivation_outcome a d records receive table cookies


/-- The original record resolver premise selects the control branch; actual
probe and detached bounded rerun retain all errors. Pure resolver success does
not establish a drain or a strict suffix of the original records. -/
theorem original_cookie_scheduled_resumption_progress (a : Activation) (d : Device) (records : List HiddenRecord)
    (summary : CookieActivationSummary) (receive : a.worker = .receiveWorker)
    (table : d.indexTable = []) (cookies : CookieOnly d)
    (resolve : resolveCookieActivation d.handshakeQueue.count records = .ok summary) :
    Campaign2.Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records ∧ s.ambient.suspended = [a])
      (scheduleTurn none) (cookieBoundedScheduler a d.handshakeQueue.count) :=
  cookieScheduler_progress a d records summary receive table cookies resolve


/-- The original full-schedule domain gives exact bounded-first-turn outcome
agreement, followed by the actual remaining turns and budget guard. It does
not guarantee successful drain on arbitrary physical ring metadata. -/
theorem original_cookie_schedule_outcome (ys : List (List UInt8)) (a : Activation)
    (d : Device) (stop : List UInt8)
    (receive : a.worker = .receiveWorker) (table : d.indexTable = []) (cookies : CookieOnly d)
    (valid : ∀ bytes ∈ ys, bytes.length = 8) (stopLen : stop.length = 8)
    (occupancy : ys.length ≤ d.handshakeQueue.count) :
    Campaign2.Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some (CookieFull.records ys stop) ∧ s.ambient.suspended = [a])
      (schedule none) (CookieFull.boundedSchedule a d.handshakeQueue.count (ys.length + 1)) :=
  CookieFull.schedule_outcome ys a d stop receive table cookies valid stopLen occupancy

/-- The original recorded batch continuation returns only with all six
queue/counter checks and its NAPI check satisfied at a present device. This
normal-return statement does not cover the recordless early branch. -/
theorem original_after_batch_recorded_drained :
    Campaign2.Product.Ensures afterBatch
      (fun s => s.ambient.hidden.isSome = true) (fun _ s => BatchDrained s) :=
  afterBatch_recorded_drained

/-- A true normal return of the original timer episode has a present device
and satisfies exactly the four final queue tests. False returns, pending-work
flags, wheel exhaustion and fairness are outside this conclusion. -/
theorem original_timer_completion (jPass : UInt64) :
    Campaign2.Product.Ensures (Env.runTimers jPass) (fun _ => True)
      (fun result final => result = true → TimerCompletionGuard final) :=
  runTimers_completion jPass

/-- Every normal recorded idle wait stores the actual end read and leaves the
modeled wheel with no timer due at that read. The claim allows an absent device
and arbitrary records, retains original Stops, and does not assert that an
operation succeeds, all work is empty, or recordless mode has the same effect. -/
theorem original_recorded_idle_wait_nothing_due :
    Campaign2.Product.Ensures idleTimers (fun s => s.ambient.hidden.isSome = true)
      (fun _ s => ∃ j, s.wg.jiffiesLast = some j ∧ NoTimerDue j s) :=
  idleTimers_recorded_nothing_due


/-- The original post-advance wait with its actual bound receipt. Erasure
covers every mode and every original error. On recorded normal return, the
stored clock equals the receipt's end read; the no-due assertion holds at
its pass bound, which may differ from that end read. No totality, queue emptiness or preceding-advance claim. -/
theorem original_recorded_advance_wait_nothing_due :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let _ ← observedAfterAdvance; pure ()) afterAdvance ∧
    Campaign2.Product.Ensures observedAfterAdvance
      (fun s => s.ambient.hidden.isSome = true)
      (fun result s => ∃ receipt, result = some receipt ∧
        s.wg.jiffiesLast = some receipt.jEnd ∧ NoTimerDue receipt.pass s) := by
  constructor
  · intro initial _
    rw [observedAfterAdvance_erase]
  · exact observedAfterAdvance_recorded_checks

/-- A normal actual wg_advance syscall certifies its own modular advance.
An actual recorded wait receipt shares that advance's bounds and establishes
its distinct end-read and wrapped-pass facts. All original Stops erase exactly;
recorded mode at syscall entry is not asserted to survive arbitrary task work. -/
theorem original_advance_operation_receipt (ticks : Nat) :
    Campaign2.Product.AgreesOn (fun _ => True)
      (do let result ← observedAdvanceOperation ticks; pure result.1)
      (syscall (.wgAdvance ticks)) ∧
    Campaign2.Product.Ensures (observedAdvanceOperation ticks) (fun _ => True)
      (fun out final => out.1 = 0 ∧ ∃ j0 j1,
        out.2.1 = some (j0,j1) ∧ j1-j0 = ticks.toUInt64 ∧
        ∀ receipt, out.2.2 = some receipt → receipt.j0 = j0 ∧ receipt.j1 = j1 ∧
          final.wg.jiffiesLast = some receipt.jEnd ∧ NoTimerDue receipt.pass final) := by
  constructor
  · intro initial _
    rw [observedAdvanceOperation_erase]
  · exact observedAdvanceOperation_checks ticks

/-- Normal return of the actual handshake-send worker loop leaves no Device
or an empty send-work queue. All record modes, queue growth and original Stops
remain; this is not a global quiescence or whole-syscall completion claim. -/
theorem original_send_workers_completion :
    Campaign2.Product.Ensures runSendWorkers (fun _ => True)
      (fun _ final => SendWorkersComplete final) :=
  runSendWorkers_completion

/-- The four final-idle syscall forms have the original execution and its
optional final clock receipt, without an entry-mode or readiness assumption. -/
theorem original_final_idle_wait_receipt (call : Syscall) (waited : HasFinalIdleWait call) :
    (do let out ← observedIdleWaitOperation call; pure out.1) = syscall call ∧
    Campaign2.Product.Ensures (observedIdleWaitOperation call) (fun _ => True)
      (fun out final => ∀ j, out.2 = some j →
        final.wg.jiffiesLast = some j ∧ NoTimerDue j final) :=
  ⟨observedIdleWaitOperation_erase call waited,observedIdleWaitOperation_checks call⟩

/-- An actual initialized domain-filter execution accepts with a retained
receive-worker pending identity and the stated empty-queue/count/NAPI tests.
This is placeholder-mode bookkeeping, not supplied-record evidence of an
unexecuted unit, nor a general physical-ring coherence claim. -/
theorem original_placeholder_pending_identity :
    ∃ audit cut d,
      executeTraceWithBoundaries CurrentBoundaryWitness.placeholderBoundaryTrace true = .ok audit ∧
      Runner.executeTrace CurrentBoundaryWitness.placeholderBoundaryTrace true = .ok audit.output ∧
      audit.boundaries[1]? = some cut ∧
      cut.index = 1 ∧ cut.result = 1 ∧ cut.after.wg.device = some d ∧
      cut.after.ambient.pendingWork = [Worker.receiveWorker.index] ∧
      cut.after.ambient.hidden.isNone = true ∧
      cut.after.ambient.suspended.isEmpty = true ∧ cut.after.wg.netRxRaised = false ∧
      d.handshakeQueue.empty = true ∧ d.handshakeQueue.count = 0 ∧
      d.handshakeQueueLen = 0 ∧ d.decryptQueue.empty = true ∧
      d.encryptQueue.empty = true ∧ d.txWorkQueue.isEmpty = true ∧
      d.sendWorkQueue.isEmpty = true ∧ d.clearWorkQueue.isEmpty = true ∧
      d.peers.toList.any (fun item => item.2.napiScheduled) = false :=
  CurrentBoundaryWitness.placeholder_accepted_pending


/-- The original allocation consumer agrees on every projected entry with a
finite evaluator. Exact-count sites perform at most their declared count of
actual encounters, with the original entry mode, unarmed bypass, early false
and errors. Arbitrary callback termination and runner progress are separate. -/
theorem original_allocation_finite (site : AllocSite) :
    Campaign2.AgreesOn (fun _ => True) (hiddenAlloc site : WG.M Bool)
      (monadLift (hiddenAllocFinite site) : WG.M Bool) :=
  hiddenAlloc_finite_agrees site


/-- Any successful finite evaluation gives the exact original modular-power
result, even with fuel below the initial exponent. Exhaustion yields no
conclusion; no runtime computation is used as a proof oracle. -/
theorem original_pow_mod_of_evaluation (b e modulus fuel : Nat) (final : PowState)
    (evaluated : powEval modulus fuel (1, b % modulus, e) = some final) :
    originalPowMod b e modulus = final.1 :=
  powMod_of_evaluation b e modulus fuel final evaluated

/-- Every actual activation is inspected with its first Stop unchanged.
The outer loop makes at most its captured occupancy plus one iteration calls.
The projected facts give the counter, suspension append and exhaustion result;
native last-iteration and section-stop provenance is proved separately by
activationExitRun_source_facts. Callback termination, adequate fuel and global
quiescence remain separate obligations. -/
theorem original_activation_exit (a : Activation) :
    (do let audit ← observedActivationExit a; pure audit.erase) =
      Campaign2.Product.inspect (Activation.run a) ∧
    Campaign2.Product.Returns (observedActivationExit a) (fun _ => True)
      (fun audit _ => ActivationExitFacts a audit) :=
  ⟨observedActivationExit_source a, observedActivationExit_facts a⟩


/-- The original scheduler's two committed activation callback sites retain an
ordered projected exit receipt, including a callback that stops. Copied
consistency trials are excluded. Exit facts alone are not an arbitrary
receipt's provenance certificate or a callback-termination theorem. -/
theorem original_schedule_committed_runs (stack : Option Worker) :
    (do let result ← CommittedRuns.observedSchedule stack; pure result.1) =
      Campaign2.Product.inspect (Env.schedule stack) ∧
    Campaign2.Product.Returns (CommittedRuns.observedSchedule stack) (fun _=>True)
      (fun result _=>∀ receipt∈result.2,ActivationExitFacts receipt.activation receipt.exit) :=
  CommittedRuns.original_schedule_journal stack

/-- A concrete normal decrypt iteration consumes exactly the head of the
represented live FIFO, or ends when that FIFO is empty. NAPI, IRQ and resched
callbacks are the actual source calls, with their ring frames discharged. -/
theorem original_decrypt_iteration_occupancy (a : Activation)
    (worker : a.worker = .decryptWorker) (deviceIndex capacity batch : Nat)
    (live : List SkbId) :
    Campaign2.Product.Ensures (Activation.iter a)
      (DecryptOccupancy.Rep deviceIndex capacity batch live)
      (fun value after => (value = .ended ↔ live = []) ∧
        DecryptOccupancy.Rep deviceIndex capacity batch live.tail after) :=
  DecryptOccupancy.original_iteration a worker deviceIndex capacity batch live

/-- Captured occupancy plus one is sufficient for a represented decrypt ring:
the actual inspection cannot report its own exhaustion. Earlier iteration and
section-stop failures remain possible. This is not callback evaluation totality
or initialized reachability of the representation. -/
theorem original_decrypt_activation_adequate (a : Activation)
    (worker : a.worker = .decryptWorker) (deviceIndex capacity batch : Nat)
    (live : List SkbId) :
    Campaign2.Product.Returns (observedActivationExit a)
      (DecryptOccupancy.Rep deviceIndex capacity batch live)
      (fun audit _ => DecryptOccupancy.NoExhaustion audit ∧ ActivationExitFacts a audit) :=
  DecryptOccupancy.original_activation a worker deviceIndex capacity batch live


/-- A normal original recorded read consumes a strict suffix, including its
passive prefix. The rest of Ambient retains its actual bookkeeping effects. -/
theorem original_hidden_record_decrease (site : HiddenSite) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (hidden site : Leanux.M (List UInt8))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.hidden_record_suffix site records

/-- Passive stripping retains an actual suffix in recorded mode. -/
theorem original_passive_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures (skipAmbient : Leanux.M Unit)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.skip_record_suffix records

/-- Peeking can strip passive records but cannot extend recorded input. -/
theorem original_peek_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures (peekHiddenSite : Leanux.M (Option Nat))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.peek_record_suffix records

/-- Every original normal reschedule preserves a suffix; true consumes at least
one record. Unsupported worker kinds and malformed records keep their Stops. -/
theorem original_reschedule_record_decrease (worker : Worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (condResched worker)
      (fun s=>s.ambient.hidden=some records)
      (fun yielded s=>RecordSuffix.Tail records s.ambient.hidden ∧
        (yielded=true→RecordSuffix.StrictTail records s.ambient.hidden)) :=
  RecordSuffix.condResched_record_suffix worker records


/-- Every original deferred call retains its exact outcome and the committed
scheduler run receipts reached before it. This extends callback coverage;
it does not establish arbitrary receipt provenance or callback termination. -/
theorem original_deferred_committed_runs (call : Leanux.Proofs.WG.Lifetimes.EnvDeferredCall) :
    (do let result ← CommittedRuns.Deferred.observed call; pure result.1) =
      Campaign2.Product.inspect call.original ∧
    Campaign2.Product.Returns (CommittedRuns.Deferred.observed call) (fun _ => True)
      (fun result _ => ∀ receipt ∈ result.2,
        ActivationExitFacts receipt.activation receipt.exit) :=
  CommittedRuns.Deferred.original_deferred_journal call

/-- Original X25519 has a completed finite evaluation on every byte-list input.
The exact clamp, point decode and encoding are retained; no curve-validity,
nonzero-output or whole-driver termination conclusion is asserted. -/
theorem original_x25519_finite_evaluation (key point : Key) :
    x25519Finite key point = some (x25519 key point) :=
  original_x25519_finite key point

/-- The actual curve wrapper has a completed finite evaluation, including
both possible values of its null-point test. -/
theorem original_curve25519_finite_evaluation (secret point : Key) :
    curve25519Finite secret point = some (curve25519 secret point) :=
  original_curve25519_finite secret point


/-- Actual native allocation retains an ambient record suffix through every
count/mode branch on normal return. No normal-return premise is guaranteed. -/
theorem original_allocation_record_suffix (records : List HiddenRecord) (site : AllocSite) :
    Campaign2.Ensures (hiddenAlloc site : WG.M Bool)
      (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.hiddenAlloc_record_suffix records site

/-- Actual packet decryption cannot extend recorded input on normal return. -/
theorem original_decrypt_packet_record_suffix (records : List HiddenRecord) (packet : RxPacket) :
    Campaign2.Ensures (decryptPacket packet)
      (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.decryptPacket_record_suffix records packet

/-- The exact RX publication cut preserves recorded suffixes; IRQ/NAPI and
final peer release are later callbacks outside this source cut. -/
theorem original_rx_publish_record_suffix (records : List HiddenRecord) (id : SkbId)
    (state : PacketState) :
    Campaign2.Ensures (Queues.RxWorkers.publishSource id state)
      (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.publish_record_suffix records id state

/-- The original dequeue/decrypt/publication source cut preserves a suffix.
Callback evaluation and full activation adequacy remain separate. -/
theorem original_rx_prepare_record_suffix (records : List HiddenRecord) :
    Campaign2.Ensures Queues.RxWorkers.prepareSource
      (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.prepare_record_suffix records

/-- Actual injection retains committed scheduler run receipts through its
original deferred continuation, including prefixes before a Stop. -/
theorem original_inject_committed_runs (family port : Nat) (msg : List UInt8)
    (tos : Nat) (ll : Bool) (dest : Nat) :
    (do let result ← CommittedRuns.Traffic.observed
          (CommittedRuns.Traffic.inject family port msg tos ll dest); pure result.1) =
      Campaign2.Product.inspect (Env.inject family port msg tos ll dest) ∧
    Campaign2.Product.Returns (CommittedRuns.Traffic.observed
      (CommittedRuns.Traffic.inject family port msg tos ll dest)) (fun _ => True)
      (fun result _ => CommittedRuns.ValidHistory result.2) :=
  CommittedRuns.Traffic.original_inject_journal family port msg tos ll dest

/-- Actual batch completion retains ordered run receipts with exact outcomes. -/
theorem original_after_batch_committed_runs :
    (do let result ← CommittedRuns.Traffic.observed CommittedRuns.Traffic.afterBatch;
        pure result.1) = Campaign2.Product.inspect Env.afterBatch ∧
    Campaign2.Product.Returns
      (CommittedRuns.Traffic.observed CommittedRuns.Traffic.afterBatch) (fun _ => True)
      (fun result _ => CommittedRuns.ValidHistory result.2) :=
  CommittedRuns.Traffic.original_afterBatch_journal

/-- Actual flood input keeps its deferred committed-run journal. -/
theorem original_flood_committed_runs (count port family : Nat)
    (messages : List (List UInt8)) :
    (do let result ← CommittedRuns.Traffic.observed
          (CommittedRuns.Traffic.flood count port family messages); pure result.1) =
      Campaign2.Product.inspect (Env.flood count port family messages) ∧
    Campaign2.Product.Returns (CommittedRuns.Traffic.observed
      (CommittedRuns.Traffic.flood count port family messages)) (fun _ => True)
      (fun result _ => CommittedRuns.ValidHistory result.2) :=
  CommittedRuns.Traffic.original_flood_journal count port family messages

/-- Actual mixed batches keep the scheduler receipts reached by their tail. -/
theorem original_batch_committed_runs (items : List Env.BatchItem) :
    (do let result ← CommittedRuns.Traffic.observed (CommittedRuns.Traffic.batch items);
        pure result.1) = Campaign2.Product.inspect (Env.batch items) ∧
    Campaign2.Product.Returns (CommittedRuns.Traffic.observed
      (CommittedRuns.Traffic.batch items)) (fun _ => True)
      (fun result _ => CommittedRuns.ValidHistory result.2) :=
  CommittedRuns.Traffic.original_batch_journal items

/-- Actual observation includes its original idle wait and committed runs. -/
theorem original_observe_committed_runs :
    (do let result ← CommittedRuns.Traffic.observed CommittedRuns.Traffic.observe;
        pure result.1) = Campaign2.Product.inspect Env.observe ∧
    Campaign2.Product.Returns
      (CommittedRuns.Traffic.observed CommittedRuns.Traffic.observe) (fun _ => True)
      (fun result _ => CommittedRuns.ValidHistory result.2) :=
  CommittedRuns.Traffic.original_observe_journal

/-- The original pipe-size rounding loop has a completed finite evaluation
for every Nat input. This does not assert termination of a whole pipe call. -/
theorem original_pipe_roundup_finite_evaluation (target : Nat) :
    PipeRoundup.finite target = some (roundupPowOfTwoUL target) ∧
      target ≤ roundupPowOfTwoUL target :=
  original_pipe_roundup_finite target


/-- Every actual syscall retains its committed scheduler-run receipt prefix,
including on failure, while preserving the exact original outcome. -/
theorem original_syscall_committed_runs (call : Syscall) :
    (do let out ← CommittedRuns.Traffic.observed (CommittedRuns.Syscalls.syscall call);
        pure out.1) = Campaign2.Product.inspect (Leanux.syscall call) ∧
    Campaign2.Product.Returns
      (CommittedRuns.Traffic.observed (CommittedRuns.Syscalls.syscall call)) (fun _ => True)
      (fun out _ => CommittedRuns.ValidHistory out.2) :=
  CommittedRuns.Syscalls.original_syscall_journal call

/-- Initialized execution retains exact JSON/indexed Stops and the committed
scheduler activation receipts. The result assumes no initial invariant or
callback law; receipt validity alone is not arbitrary-history provenance. -/
theorem original_initialized_committed_runs (trace : Runner.Trace) (placeholders : Bool) :
    (CommittedRuns.Initialized.inspection trace placeholders).1.map Prod.fst =
      Runner.executeTrace trace placeholders ∧
    ∀ receipt ∈ (CommittedRuns.Initialized.inspection trace placeholders).2,
      ActivationExitFacts receipt.activation receipt.exit :=
  CommittedRuns.Initialized.original_initialized_journal trace placeholders

/-- Actual peer release preserves recorded suffixes through every normal
reference/null branch, retaining queued-release and missing-owner Stops. -/
theorem original_peer_release_record_suffix (records : List HiddenRecord)
    (peer : Option PeerId) :
    Campaign2.Ensures (peerPut peer) (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.peerPut_record_suffix records peer

/-- Actual key release preserves recorded suffixes in either release mode. -/
theorem original_key_release_record_suffix (records : List HiddenRecord)
    (key : Option KeypairId) (now : Bool) :
    Campaign2.Ensures (keypairPut key now) (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.keypairPut_record_suffix records key now

/-- Actual responder confirmation and its release tail preserve suffixes. -/
theorem original_confirmation_record_suffix (records : List HiddenRecord)
    (peer : PeerId) (key : KeypairId) :
    Campaign2.Ensures (receivedWithKeypair peer key)
      (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.confirmation_record_suffix records peer key

/-- Actual replay validation preserves the record suffix on normal return;
malformed counters retain their original failures. -/
theorem original_counter_validation_record_suffix (records : List HiddenRecord)
    (key : KeypairId) (nonce : Nat) :
    Campaign2.Ensures (counterValidate key nonce)
      (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.counterValidate_record_suffix records key nonce

/-- Actual selected cut consumption retains a recorded suffix. -/
theorem original_cut_sites_record_suffix (sites : List HiddenSite)
    (records : List HiddenRecord) :
    Campaign2.Ensures (skipCutSites sites : WG.M (List Nat))
      (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.cutSites_record_suffix sites records

/-- Either original timer jitter loop consumes a strict suffix on normal return. -/
theorem original_jitter_record_decrease (site : TimerDiscipline.JitterSite)
    (records : List HiddenRecord) :
    Campaign2.Ensures (jitterBelowRekeyTimeout site.hiddenSite)
      (fun s => s.ambient.hidden = some records)
      (fun _ s => RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.jitter_record_decrease site records

/-- The original pipe teardown has an exact finite evaluation, including
all original failures and actual buffer-release calls. -/
theorem original_pipe_free_finite_evaluation (pipe : PipeId) :
    Leanux.freePipeInfo pipe = PipeFree.finite pipe :=
  original_free_pipe_info_finite pipe

/-- Every receipt in the initialized journal has an actual native call entry
and exit, together with its activation-specific exit facts. -/
theorem original_initialized_run_sources (trace : Runner.Trace) (placeholders : Bool) :
    (CommittedRuns.Initialized.inspection trace placeholders).1.map Prod.fst =
      Runner.executeTrace trace placeholders ∧
    ∀ receipt ∈ (CommittedRuns.Initialized.inspection trace placeholders).2,
      CommittedRuns.SourceReceipt receipt ∧
        ActivationExitFacts receipt.activation receipt.exit :=
  CommittedRuns.Initialized.original_initialized_source_receipts trace placeholders

/-- The actual write-to-out helper has an exact finite evaluation including
allocation and original failures, with no successful-write premise. -/
theorem original_pipe_write_finite_evaluation (iocb : Kiocb) (filp : File)
    (pipe : PipeId) (src : IovIter) :
    pipeWriteToOut iocb filp pipe src = PipeWrite.finite iocb filp pipe src :=
  original_pipe_write_to_out_finite iocb filp pipe src

/-- Actual timer arming preserves a recorded suffix through its complete
wheel placement and original failures. -/
theorem original_timer_arm_record_suffix (records : List HiddenRecord)
    (peer : PeerId) (timer : PeerTimer) (delay : Nat) (caller : Option UInt64) :
    Campaign2.Ensures (armTimer peer timer delay caller)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.armTimer_record_suffix records peer timer delay caller

/-- Actual receive timer handling now has its concrete arming dependency
discharged; normal return retains a recorded suffix. -/
theorem original_receive_timer_record_suffix (records : List HiddenRecord) (peer : PeerId) :
    Campaign2.Ensures (timersDataReceived peer)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.timersDataReceived_record_suffix records peer


/-- The complete original read has an exact finite evaluator, including its
concrete wake/timestamp callbacks and every original failure. -/
theorem original_pipe_read_finite_evaluation (iocb : Kiocb) (count : Nat) :
    pipeRead iocb count = PipeRead.finite iocb count :=
  original_pipe_read_finite iocb count

/-- The complete original write reuses the finite inner evaluator and keeps
its actual wake/time suffix and all original outcomes. -/
theorem original_pipe_write_complete_finite_evaluation (iocb : Kiocb) (src : IovIter) :
    pipeWrite iocb src = PipeWriteOuter.finite iocb src :=
  original_pipe_write_finite iocb src

/-- Actual staging preserves a recorded suffix on normal return; this is
neither strict record decrease nor a successful-return premise for termination. -/
theorem original_staged_record_suffix (records : List HiddenRecord) (peer : PeerId) :
    Campaign2.Ensures (sendStagedPackets peer)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.staged_record_suffix records peer

/-- The actual keepalive caller has the same concrete normal record-suffix
contract, with its allocation and staging dependencies discharged. -/
theorem original_keepalive_record_suffix (records : List HiddenRecord) (peer : PeerId) :
    Campaign2.Ensures (sendKeepalive peer)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.keepalive_record_suffix records peer

open RecordSuffix in
theorem original_clear_callback_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) :=
  RecordSuffix.original_clear_callback_record_suffix records pid

open RecordSuffix in
theorem original_clear_worker_record_decrease (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.runOneClearWorker
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>StrictTail records s.ambient.hidden) :=
  RecordSuffix.original_clear_worker_record_decrease records

open RecordSuffix Leanux.Env in
/-- A false receive-step return is the actual empty-ring cut and preserves WG state and hidden records. -/
theorem original_receive_empty_return (entry : Campaign2.Snapshot) :
    Campaign2.Ensures WG.receiveStep (fun s => s = entry)
      (fun value final => value = false →
        (∃ d, entry.wg.device = some d ∧ d.handshakeQueue.peek = none) ∧
        final.wg = entry.wg ∧ final.ambient.hidden = entry.ambient.hidden) :=
  RecordSuffix.original_receive_empty_return entry

open RecordSuffix Leanux.Env in
/-- An ended receive iteration starts with an empty ring and leaves WG state and hidden records unchanged. -/
theorem original_receive_ended_return (active : Activation)
    (receive : active.worker = .receiveWorker) (entry : Campaign2.Product.Snapshot) :
    Campaign2.Product.Ensures (Activation.iter active) (fun s => s = entry)
      (fun value final => value = .ended →
        (∃ d, entry.wg.device = some d ∧ d.handshakeQueue.peek = none) ∧
        final.wg = entry.wg ∧ final.ambient.hidden = entry.ambient.hidden) :=
  RecordSuffix.original_receive_ended_return active receive entry

open RecordSuffix Leanux.Env in
/-- An original receive activation starting empty strictly consumes supplied records on normal completion. -/
theorem original_empty_receive_activation_decrease (active : Activation)
    (receive : active.worker = .receiveWorker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run active)
      (fun s => s.ambient.hidden = some records ∧
        ∃ d, s.wg.device = some d ∧ d.handshakeQueue.peek = none)
      (fun _ s => StrictTail records s.ambient.hidden) :=
  RecordSuffix.original_empty_receive_activation_decrease active receive records

open RecordSuffix Leanux.Env in
/-- The original activation audit retains its actual final empty receive cut and section-stop record decrease. -/
theorem original_receive_terminal_records (active : Activation)
    (receive : active.worker = .receiveWorker) :
    Campaign2.Product.Returns (observedActivationExit active) (fun _ => True)
      (fun audit _ => ReceiveTerminal audit ∧ ActivationExitFacts active audit) :=
  RecordSuffix.original_receive_terminal_records active receive

/-- Actual receive completion preserves a suffix of supplied records on
normal return, with the endpoint and allowed-IP dependencies discharged. -/
theorem original_consume_data_done_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Campaign2.Ensures (consumeDataDone pid pkt ep)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.consumeDataDone_record_suffix records pid pkt ep

/-- The exact product lift retains the same supplied-record suffix on normal
return; this contract does not assert that execution completes. -/
theorem original_product_consume_data_done_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (pkt : RxPacket) (ep : Endpoint) :
    Campaign2.Product.Ensures (liftWG (consumeDataDone pid pkt ep))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.consumeDataDone_product_record_suffix records pid pkt ep


/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_create_initiation_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (createInitiation pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.createInitiation_record_suffix records pid

/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_create_response_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (createResponse pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.createResponse_record_suffix records pid

/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_session_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (beginSession pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.beginSession_record_suffix records pid

/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_consume_initiation_record_suffix (records : List HiddenRecord) (message : List UInt8) :
    Campaign2.Ensures (consumeInitiation message)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.consumeInitiation_record_suffix records message

/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_consume_response_record_suffix (records : List HiddenRecord) (message : List UInt8) :
    Campaign2.Ensures (consumeResponse message)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.consumeResponse_record_suffix records message

/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_cookie_consume_record_suffix (records : List HiddenRecord) (message : List UInt8) :
    Campaign2.Ensures (cookieMessageConsume message)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.cookieMessageConsume_record_suffix records message

/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_handshake_response_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeResponse pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.sendHandshakeResponse_record_suffix records pid

/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_handshake_initiation_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (sendHandshakeInitiation pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.sendHandshakeInitiation_record_suffix records pid

/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_handshake_receive_record_suffix (records : List HiddenRecord) (message : List UInt8) (src : SkbSource) :
    Campaign2.Ensures (receiveHandshakePacket message src)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.receiveHandshakePacket_record_suffix records message src

/-- The complete original call preserves a supplied-record suffix on normal return. -/
theorem original_receive_step_record_suffix (records : List HiddenRecord)  :
    Campaign2.Ensures (receiveStep )
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.receiveStep_record_suffix records

/-- Every normally returning original receive activation strictly consumes supplied records,
including activations that start with queued packets. -/
theorem original_receive_activation_record_decrease (a : Activation)
    (worker : a.worker=.receiveWorker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run a)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.receive_activation_record_decrease a worker records

/-- The selected original handshake send dispatch strictly consumes records on normal return. -/
theorem original_send_worker_record_decrease (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.runOneSendWorker
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.send_worker_record_decrease records

/-- Original inner delivery has concrete routing, loopback and WG transmit dependencies. -/
theorem original_inner_delivery_record_suffix (records : List HiddenRecord) (bytes : List UInt8) :
    Campaign2.Product.Ensures (Env.deliverInner bytes)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.deliverInner_record_suffix records bytes

/-- Original WG transmission preserves supplied-record suffixes through every normal arm. -/
theorem original_xmit_record_suffix (records : List HiddenRecord) (family addr : Nat)
    (packets : List Packet) (mtu : Nat) :
    Campaign2.Ensures (wgXmit family addr packets mtu)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.wgXmit_record_suffix records family addr packets mtu

/-- The actual packet encryption has its concrete checksum dependency discharged. -/
theorem original_encrypt_packet_record_suffix (records : List HiddenRecord)
    (key : KeypairId) (packet : DataPacket) :
    Campaign2.Product.Ensures (encryptPacket Env.checksumHelp key packet)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.encryptPacket_record_suffix records key packet

/-- The actual socket caller has concrete IPv4 and IPv6 routing and loopback contracts. -/
theorem original_socket_packet_record_suffix (records : List HiddenRecord) (pid : PeerId) (bytes : List UInt8) (ds : Nat) :
    Campaign2.Ensures (sendSkbToPeer pid bytes ds)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.sendSkbToPeer_record_suffix records pid bytes ds

/-- The actual socket caller has concrete IPv4 and IPv6 routing and loopback contracts. -/
theorem original_socket_buffer_record_suffix (records : List HiddenRecord) (pid : PeerId) (bytes : List UInt8) :
    Campaign2.Ensures (sendBufferToPeer pid bytes)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.sendBufferToPeer_record_suffix records pid bytes

/-- The actual socket caller has concrete IPv4 and IPv6 routing and loopback contracts. -/
theorem original_socket_reply_record_suffix (records : List HiddenRecord) (src : SkbSource) (bytes : List UInt8) :
    Campaign2.Ensures (sendBufferAsReplyToSkb src bytes)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.sendBufferAsReplyToSkb_record_suffix records src bytes

/-- The original poll uses concrete consume/GRO/inner-delivery suffix contracts. -/
theorem original_poll_record_suffix (records : List HiddenRecord) (pid : PeerId) (budget : Nat) :
    Campaign2.Product.Ensures (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.rxPoll_record_suffix records pid budget

/-- The original NAPI caller preserves supplied-record suffixes on normal return. -/
theorem original_napi_softirq_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.napiSoftirq
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.softirq_record_suffix records

/-- The original NAPI caller preserves supplied-record suffixes on normal return. -/
theorem original_napi_inline_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.pollScheduledInline
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.inline_record_suffix records

/-- The original NAPI caller preserves supplied-record suffixes on normal return. -/
theorem original_napi_irq_exit_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.napiIrqExit
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.irqExit_record_suffix records

/-- Every normally returning original encrypt activation strictly consumes
supplied records, with the actual NAPI callbacks discharged. -/
theorem original_encrypt_activation_record_decrease (a : Activation)
    (worker : a.worker=.encryptWorker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run a)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.encryptActivation_record_strict a worker records

/-- Every normally returning original decrypt activation strictly consumes
supplied records, with the actual NAPI callbacks discharged. -/
theorem original_decrypt_activation_record_decrease (a : Activation)
    (worker : a.worker=.decryptWorker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run a)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.decryptActivation_record_strict a worker records


/-- Original transmit completion retains supplied-record suffixes through
its concrete socket, timer, key freshness and release calls. -/
theorem original_data_done_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (item : List SkbId) :
    Campaign2.Ensures (createDataDone pid item)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.createDataDone_record_suffix records pid item

/-- The complete original transmit step retains a supplied-record suffix. -/
theorem original_tx_step_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (txStep pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.txStep_record_suffix records pid

/-- The actual preceding encrypt iteration and NAPI callbacks preserve the
record suffix used by the subsequent transmit iteration. -/
theorem original_crypt_ahead_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Product.Ensures (Env.cryptAhead pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.cryptAhead_record_suffix records pid

/-- The original transmit activation iteration retains records, and a yielded
return strictly consumes them, including its actual crypt-ahead prelude. -/
theorem original_tx_iteration_record_effect (a : Activation) (worker : a.worker=.txWorker)
    (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.iter a)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>RecordSuffix.Tail records s.ambient.hidden ∧
        (result=.yielded→RecordSuffix.StrictTail records s.ambient.hidden)) :=
  RecordSuffix.txActivation_record_effect a worker records

/-- Every normally returning original transmit activation strictly consumes
supplied records with all actual encrypt/NAPI callbacks discharged. -/
theorem original_tx_activation_record_decrease (a : Activation) (worker : a.worker=.txWorker)
    (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run a)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.txActivation_record_strict a worker records


/-- All five original timer callbacks retain supplied-record suffixes. -/
theorem original_timer_callback_record_suffix (records : List HiddenRecord)
    (pid : PeerId) (timer : PeerTimer) :
    Campaign2.Ensures (timerCallback pid timer)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.timerCallback_record_suffix records pid timer

/-- The actual timer section wrapper strictly consumes records on normal
return. Wheel-selected worker/timer matching belongs to the enclosing caller. -/
theorem original_timer_section_record_decrease (records : List HiddenRecord)
    (worker : Worker) (pid : PeerId) (timer : PeerTimer) :
    Campaign2.Product.Ensures (Env.runTimerSection worker (liftWG (timerCallback pid timer)))
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.timerSection_record_decrease records worker pid timer

/-- A dispatch that reports work strictly consumes the actual supplied records. -/
theorem original_dispatch_record_effect (worker : Worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Env.dispatch worker)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>RecordSuffix.Tail records s.ambient.hidden ∧
        (result=true→RecordSuffix.StrictTail records s.ambient.hidden)) :=
  RecordSuffix.dispatch_record_suffix worker records

/-- Every normally continuing original scheduler turn consumes records. -/
theorem original_scheduler_turn_record_decrease (stack : Option Worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (scheduleTurn stack)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>RecordSuffix.Tail records s.ambient.hidden ∧
        (result=turnContinue→RecordSuffix.StrictTail records s.ambient.hidden)) :=
  RecordSuffix.scheduleTurn_record_suffix stack records

/-- Whole scheduling preserves a supplied-record suffix on normal return. -/
theorem original_schedule_record_suffix (stack : Option Worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Env.schedule stack)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.schedule_record_suffix stack records

/-- Original fixture delivery retains the actual remaining records. -/
theorem original_delivery_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.deliverSent
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.deliverSent_record_suffix records

/-- The actual scheduler followed by delivery retains supplied-record suffixes. -/
theorem original_crypt_workers_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.runCryptWorkers
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.runCryptWorkers_record_suffix records


/-- The original timer-unit factor strictly consumes its supplied records. -/
theorem original_timer_unit_record_decrease (records : List HiddenRecord) (worker : Worker)
    (pid : PeerId) (timer : PeerTimer) (entry : WheelEntry) (step : Option UInt64) :
    Campaign2.Product.Ensures
      (TimerDiscipline.timerDispatchUnit_variant worker pid timer entry step)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.timerDispatchUnit_record_strict records worker pid timer entry step

/-- All branches of the whole actual timer loop retain supplied-record suffixes. -/
theorem original_timer_loop_record_suffix (records : List HiddenRecord) (bound : UInt64) :
    Campaign2.Product.Ensures (Env.runTimers bound)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.runTimers_record_suffix records bound

/-- Each normal committed activation in the initialized journal strictly
consumes its own supplied records, including before a later enclosing Stop. -/
theorem initialized_committed_activation_record_decrease
    (trace : Runner.Trace) (placeholders : Bool) :
    (CommittedRuns.Initialized.inspection trace placeholders).1.map Prod.fst =
      Runner.executeTrace trace placeholders ∧
    ∀ receipt ∈ (CommittedRuns.Initialized.inspection trace placeholders).2,
      ∀ records final, receipt.before.ambient.hidden=some records →
        receipt.exit.erase=.ok ((),final) →
          RecordSuffix.StrictTail records final.ambient.hidden :=
  CommittedRuns.Initialized.original_initialized_record_decrease trace placeholders


/-- The actual record-derived scheduler budget cannot end normally with
the exhaustion marker. Callback Stops remain possible. -/
theorem original_scheduler_record_budget_adequate (stack : Option Worker)
    (records : List HiddenRecord) :
    Campaign2.Product.Ensures
      (forIn (List.range' 0 (records.length+1)) ((none,()) : Option Unit × Unit)
        (fun _ _=>scheduleTurn stack))
      (fun s=>s.ambient.hidden=some records) (fun result _=>result=(some (),())) :=
  RecordSuffix.scheduler_loop_budget_adequate stack records

/-- Removing only the scheduler's unreachable outer exhaustion continuation
retains every original callback result and Stop. -/
theorem original_scheduler_record_budget_source (stack : Option Worker)
    (records : List HiddenRecord) :
    Campaign2.Product.AgreesOn (fun s=>s.ambient.hidden=some records)
      (Env.schedule stack)
      (do
        let _ ← forIn (List.range' 0 (records.length+1)) ((none,()) : Option Unit × Unit)
          (fun _ _=>scheduleTurn stack)
        pure ()) :=
  RecordSuffix.scheduler_record_budget_source stack records


/-- A normally continuing original timer-loop turn strictly consumes records,
including its actual send, clear, timer and crypt-scheduling alternatives. -/
theorem original_timer_turn_record_decrease (bound : UInt64) (iteration : Nat)
    (control : Bool × Option UInt64) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (TimerDiscipline.timerOuterTurn bound iteration control)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>RecordSuffix.Tail records s.ambient.hidden ∧
        ∀ next, result=ForInStep.yield next → RecordSuffix.StrictTail records s.ambient.hidden) :=
  RecordSuffix.timerOuterTurn_record_strict bound iteration control records


/-- An actual continuing send-worker turn strictly consumes supplied records. -/
theorem original_send_turn_record_decrease (records : List HiddenRecord)
    (index : Nat) (state : Option Unit×Unit) :
    Campaign2.Product.Ensures (sendCompletionTurn index state)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>RecordSuffix.Tail records s.ambient.hidden ∧
        (∀ value,result=.yield value→RecordSuffix.StrictTail records s.ambient.hidden)) :=
  RecordSuffix.sendCompletionTurn_record_suffix records index state

/-- The send loop's recorded budget reaches its actual empty-queue return
on every normal loop result. -/
theorem original_send_loop_record_budget_adequate (records : List HiddenRecord) :
    Campaign2.Product.Ensures
      (forIn (List.range' 0 (records.length+1)) ((none,()) : Option Unit×Unit) sendCompletionTurn)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>result.1.isSome=true ∧ ∃ d,s.wg.device=some d ∧ d.sendWorkQueue=[]) :=
  RecordSuffix.sendWorkers_loop_budget_adequate records

/-- The whole original send-worker caller retains a supplied-record suffix. -/
theorem original_send_workers_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.runSendWorkers
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.runSendWorkers_record_suffix records

/-- The original send caller agrees on every outcome with its same prefix
and captured loop with only the unreachable exhaustion continuation removed. -/
theorem original_send_workers_record_budget_source (records : List HiddenRecord) :
    Campaign2.Product.AgreesOn (fun s=>s.ambient.hidden=some records)
      Env.runSendWorkers
      (do
        if (←getWG).dev.isNone then return
        requireNoCryptWork
        modifyWG fun g=>{g with queuedThisCall:=[]}
        let _←forIn (List.range' 0 (records.length+1))
          ((none,()) : Option Unit×Unit) sendCompletionTurn
        pure ()) :=
  RecordSuffix.sendWorkers_record_budget_source records

/-- A normal original timer call has its own valid episode and an actual
done turn at its captured budget, or the original absent-device branch. -/
theorem original_timer_record_budget_adequate (bound : UInt64) (records : List HiddenRecord) :
    Campaign2.Product.Observes (Env.runTimers bound)
      (fun s=>s.ambient.hidden=some records)
      (fun entry outcome=>match outcome with
        | .error _=>True
        | .ok (result,final)=>∃ receipt,
            TimerDiscipline.OuterTimerEpisodeValid bound entry receipt result final ∧
            RecordSuffix.TimerEpisodeBudgetDone records receipt) :=
  RecordSuffix.runTimers_record_budget bound records

/-- The actual recorded batch loop retains suffixes before its completion guard. -/
theorem original_batch_loop_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures afterBatchRecordedLoop
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>RecordSuffix.Tail records s.ambient.hidden) :=
  RecordSuffix.afterBatchRecordedLoop_record_suffix records

/-- The actual batch turn strictly consumes records whenever it continues. -/
theorem original_batch_turn_record_decrease (iteration : Nat) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (RecordSuffix.afterBatchRecordedTurn iteration ())
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>RecordSuffix.Tail records s.ambient.hidden ∧
        (result=.yield ()→RecordSuffix.StrictTail records s.ambient.hidden)) :=
  RecordSuffix.batchTurn_record_effect iteration records

/-- Increasing the recorded batch loop's original budget preserves its exact
outcome and final projected state, before the subsequent drain suffix. -/
theorem original_batch_loop_record_budget_adequate (records : List HiddenRecord) (extra : Nat) :
    Campaign2.Product.AgreesOn (fun s=>s.ambient.hidden=some records)
      afterBatchRecordedLoop
      (do
        let _ ← forIn (List.range' 0 (records.length+1+extra)) () RecordSuffix.afterBatchRecordedTurn
        pure ()) :=
  RecordSuffix.batch_loop_budget_adequate records extra

/-- Exact finite evaluation of the original create initiation call,
for every entry and input mode, retaining all original refusals and Stops. -/
theorem original_create_initiation_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.createInitiation pid)
      (HandshakeFinite.createInitiation pid) :=
  HandshakeFinite.original_createInitiation_finite pid

/-- Exact finite evaluation of the original create response call,
for every entry and input mode, retaining all original refusals and Stops. -/
theorem original_create_response_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.createResponse pid)
      (HandshakeFinite.createResponse pid) :=
  HandshakeFinite.original_createResponse_finite pid

/-- Exact finite evaluation of the original consume initiation call,
for every entry and input mode, retaining all original refusals and Stops. -/
theorem original_consume_initiation_finite (msg : List UInt8) :
    Campaign2.AgreesOn (fun _ => True) (WG.consumeInitiation msg)
      (ConsumerFinite.initiation msg) :=
  ConsumerFinite.original_initiation_finite msg

/-- Exact finite evaluation of the original consume response call,
for every entry and input mode, retaining all original refusals and Stops. -/
theorem original_consume_response_finite (msg : List UInt8) :
    Campaign2.AgreesOn (fun _ => True) (WG.consumeResponse msg)
      (ConsumerFinite.response msg) :=
  ConsumerFinite.original_response_finite msg

/-- Exact finite evaluation of the original send buffer call,
for every entry and input mode, retaining all original refusals and Stops. -/
theorem original_send_buffer_finite (pid : PeerId) (bytes : List UInt8) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendBufferToPeer pid bytes)
      (HandshakeFinite.sendBuffer pid bytes) :=
  HandshakeFinite.original_sendBuffer_finite pid bytes

/-- Exact finite evaluation of the original send response call,
for every entry and input mode, retaining all original refusals and Stops. -/
theorem original_send_response_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendHandshakeResponse pid)
      (HandshakeFinite.sendResponse pid) :=
  HandshakeFinite.original_sendResponse_finite pid

/-- Exact finite evaluation of the original send initiation call,
for every entry and input mode, retaining all original refusals and Stops. -/
theorem original_send_initiation_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendHandshakeInitiation pid)
      (HandshakeFinite.sendInitiation pid) :=
  HandshakeFinite.original_sendInitiation_finite pid

/-- Exact finite evaluation of the original handshake send worker call,
for every entry and input mode, retaining all original refusals and Stops. -/
theorem original_handshake_send_worker_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.handshakeSendWorker pid)
      (HandshakeFinite.sendWorker pid) :=
  HandshakeFinite.original_sendWorker_finite pid

/-- Exact finite evaluation of the original keepalive call,
for every entry and input mode, retaining all original refusals and Stops. -/
theorem original_keepalive_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendKeepalive pid)
      (HandshakeFinite.keepalive pid) :=
  HandshakeFinite.original_keepalive_finite pid

/-- Exact finite evaluation of the whole original ratelimiter
for every input mode, preserving all refusals and Stops. -/
theorem original_ratelimiter_finite (src : SkbSource) :
    Campaign2.AgreesOn (fun _ => True) (WG.ratelimiterAllow src)
      (HandshakeFinite.ratelimiter src) :=
  HandshakeFinite.original_ratelimiter_finite src

/-- Exact finite evaluation of the whole original cookie validation
for every input mode, preserving all refusals and Stops. -/
theorem original_cookie_validation_finite (msg : List UInt8) (src : SkbSource) (checkCookie : Bool) :
    Campaign2.AgreesOn (fun _ => True) (WG.cookieValidatePacket msg src checkCookie)
      (HandshakeFinite.validateCookie msg src checkCookie) :=
  HandshakeFinite.original_validateCookie_finite msg src checkCookie

/-- Exact finite evaluation of the whole original reply sender
for every input mode, preserving all refusals and Stops. -/
theorem original_reply_sender_finite (src : SkbSource) (bytes : List UInt8) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendBufferAsReplyToSkb src bytes)
      (HandshakeFinite.sendReply src bytes) :=
  HandshakeFinite.original_sendReply_finite src bytes

/-- Exact finite evaluation of the whole original cookie sender
for every input mode, preserving all refusals and Stops. -/
theorem original_cookie_sender_finite (msg : List UInt8) (src : SkbSource) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendHandshakeCookie msg src)
      (HandshakeFinite.sendCookie msg src) :=
  HandshakeFinite.original_sendCookie_finite msg src

/-- Exact finite evaluation of the whole original handshake reception
for every input mode, preserving all refusals and Stops. -/
theorem original_handshake_reception_finite (msg : List UInt8) (src : SkbSource) :
    Campaign2.AgreesOn (fun _ => True) (WG.receiveHandshakePacket msg src)
      (HandshakeFinite.reception msg src) :=
  HandshakeFinite.original_reception_finite msg src

/-- Complete original receive-step finite evaluation, including empty-ring,
callback refusal and every original Stop outcome. -/
theorem original_receive_step_finite :
    Campaign2.AgreesOn (fun _ => True) WG.receiveStep HandshakeFinite.receiveStep :=
  HandshakeFinite.original_receiveStep_finite

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_activation_iteration_finite (a : Activation) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.Activation.iter a) (ActivationFinite.iteration a) :=
  ActivationFinite.original_iteration_finite a

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_activation_run_finite (a : Activation) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.Activation.run a) (ActivationFinite.run a) :=
  ActivationFinite.original_run_finite a

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_activation_dispatch_finite (worker : Worker) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.dispatch worker) (ActivationFinite.dispatch worker) :=
  ActivationFinite.original_dispatch_finite worker

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_scheduler_consistent_finite (a : Activation) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.Activation.consistent a) (SchedulerFinite.consistent a) :=
  SchedulerFinite.original_consistent_finite a

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_scheduler_schedule_finite (stack : Option Worker) :
    Campaign2.Product.AgreesOn (fun _ => True) (Env.schedule stack) (SchedulerFinite.schedule stack) :=
  SchedulerFinite.original_schedule_finite stack

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_peer_precompute_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.precomputeStaticStatic pid) (PeerFinite.precompute pid) :=
  PeerFinite.original_precompute_finite pid

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_peer_setPrivate_finite (key : Key) :
    Campaign2.AgreesOn (fun _ => True) (WG.setStaticIdentityPrivateKey key) (PeerFinite.setPrivate key) :=
  PeerFinite.original_setPrivate_finite key

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_peer_handshakeInit_finite (pid : PeerId) (psk : Option Key) :
    Campaign2.AgreesOn (fun _ => True) (WG.handshakeInit pid psk) (PeerFinite.handshakeInit pid psk) :=
  PeerFinite.original_handshakeInit_finite pid psk

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_peer_create_finite (key : Key) (psk : Option Key) :
    Campaign2.AgreesOn (fun _ => True) (WG.peerCreate key psk) (PeerFinite.create key psk) :=
  PeerFinite.original_create_finite key psk

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_allowed_allocate_finite (site : AllocSite) (node : AipNode) :
    Campaign2.AgreesOn (fun _ => True) (liftAip (WG.allocNode site node))
      (liftAip (AllowedFinite.allocate site node)) :=
  AllowedFinite.original_allocate_finite site node

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_allowed_add_finite (root : Slot) (bits key cidr : Nat) (peer : Option PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.add root bits key cidr peer)
      (AllowedFinite.add root bits key cidr peer) :=
  AllowedFinite.original_add_finite root bits key cidr peer

/-- Exact finite native evaluation; original refusals and Stops remain unchanged. -/
theorem original_allowed_insert_finite (family addr cidr : Nat) (peer : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.insert family addr cidr peer)
      (AllowedFinite.insert family addr cidr peer) :=
  AllowedFinite.original_insert_finite family addr cidr peer

end Leanux.Proofs.WG.Progress
