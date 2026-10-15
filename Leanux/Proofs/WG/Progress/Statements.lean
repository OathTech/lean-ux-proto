import Leanux.Proofs.WG.Progress.ObservationBridge
import Leanux.Proofs.WG.Progress.CutClaims
import Leanux.Proofs.WG.Progress.FlushQueueClaims
import Leanux.Proofs.WG.Progress.PowSource

/-! Projected H5 contracts. Inspection adapters report the exact original
outcomes from the same concrete entry; their totality is not a claim that the
inspected operation succeeds. Generic callback laws are explicitly generic. -/
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env Campaign2

/-- Historical accepted runner counterexample over the registered mirror revision. -/
theorem original_pending_batch_accepted : accepted = true :=
  SourceClaims.original_pending_batch_accepted

/-- The actual initialized two-operation fixture's pending receive backlog. -/
theorem original_pending_batch_state : backlog = some (1, 1, [1], some 0, 0, false) :=
  SourceClaims.original_pending_batch_state

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
  | ok pair => simp [probeObservation, h, probeResult, observeResult, Except.map, eq_comm]
  | error err => cases err <;> simp [probeObservation, h, probeResult, observeResult, Except.map]

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
  | ok pair => simp [probeObservation, h, probeResult, observeResult, Except.map]
  | error err => cases err <;> simp [probeObservation, h, probeResult, observeResult, Except.map, eq_comm]

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
    (empty : d.handshakeQueue.isEmpty = true ∧ d.decryptQueue.empty = true ∧
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
    Ensures (runFlushedSendWork pid) (fun entry => entry.wg.device = some d)
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
    Ensures (runFlushedClearWork pid) (fun entry => entry.wg.device = some d)
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

end Leanux.Proofs.WG.Progress
