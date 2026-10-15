import Leanux.Proofs.WG.Progress.CookieSchedulerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- The actual occupancy budget suffices throughout this closed queue domain.
Errors retain the exact original hidden-record diagnostics. -/
theorem cookieActivation_outcome (a : Activation) (d : Device) (records : List HiddenRecord)
    (receive : a.worker = .receiveWorker) (table : d.indexTable = []) (cookies : CookieOnly d) :
    Campaign2.Observes (Activation.run a)
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records)
      (fun entry outcome => outcome =
        match resolveCookieActivation d.handshakeQueue.length records with
        | .error error => .error error
        | .ok summary => .ok ((), cookieActivationSnapshot a d entry summary)) := by
  intro w pre
  have run := cookieActivation_run a w d records receive pre.1 table cookies pre.2
  unfold Campaign2.observeResult
  rw [run]
  cases result : resolveCookieActivation d.handshakeQueue.length records with
  | error error => rfl
  | ok summary =>
    simp only [Except.map, cookieActivation_snapshot]

/-- After the original singleton branch removes the old suspended activation,
the committed run either reports a hidden-record error or consumes a strict
record suffix and drains the queue or yields after exactly one item. -/
theorem cookieResumption_progress (a : Activation) (d : Device) (records : List HiddenRecord)
    (receive : a.worker = .receiveWorker) (table : d.indexTable = []) (cookies : CookieOnly d) :
    Campaign2.Observes (resumeCandidates none [a])
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records)
      (fun entry outcome =>
        (∃ message, outcome = .error (.hidden message)) ∨
        ∃ summary, resolveCookieActivation d.handshakeQueue.length records = .ok summary ∧
          outcome = .ok (turnContinue, cookieActivationSnapshot a d
            {entry with ambient := {entry.ambient with suspended := entry.ambient.suspended.filter (· != a)}}
            summary) ∧
          CookieActivationProgress d.handshakeQueue.length records summary ∧
          (summary.yielded = true → summary.processed = 1)) := by
  intro w pre
  have run := cookieActivation_run a (detached w a) d records receive pre.1 table cookies pre.2
  have progress := resolveCookieActivation_progress d.handshakeQueue.length records
  unfold Campaign2.observeResult
  rw [resumeCandidates_singleton, run]
  cases result : resolveCookieActivation d.handshakeQueue.length records with
  | error error =>
    simp only [result] at progress
    rcases progress with ⟨message, rfl⟩
    exact Or.inl ⟨message, rfl⟩
  | ok summary =>
    simp only [result] at progress
    refine Or.inr ⟨summary, rfl, ?_, progress, ?_⟩
    · simp [bind, pure, Except.bind, Except.pure, Except.map,
        cookieActivation_snapshot, cookieDetached_snapshot]
      rfl
    · exact resolveCookieActivation_yield_count d.handshakeQueue.length records summary result

/-- One complete original scheduler turn derives the singleton candidate by
probing the original activation, removes it, and commits the successful run.
Only pure record validation is assumed; no execution success is a premise. -/
theorem cookieScheduler_progress (a : Activation) (d : Device) (records : List HiddenRecord)
    (summary : CookieActivationSummary) (receive : a.worker = .receiveWorker)
    (table : d.indexTable = []) (cookies : CookieOnly d)
    (resolve : resolveCookieActivation d.handshakeQueue.length records = .ok summary) :
    Campaign2.Observes (scheduleTurn none)
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records ∧ s.ambient.suspended = [a])
      (fun entry outcome =>
        outcome = .ok (turnContinue, cookieActivationSnapshot a d
          {entry with ambient := {entry.ambient with suspended := []}} summary) ∧
        CookieActivationProgress d.handshakeQueue.length records summary ∧
        (summary.yielded = true → summary.processed = 1)) := by
  intro w pre
  have run := cookieScheduler_run a w d records summary receive pre.1 table cookies pre.2.1 pre.2.2 resolve
  have progress := resolveCookieActivation_progress d.handshakeQueue.length records
  rw [resolve] at progress
  refine ⟨?_, progress, resolveCookieActivation_yield_count _ records summary resolve⟩
  unfold Campaign2.observeResult
  rw [run]
  simp only [Except.map, cookieActivation_snapshot]
  change Except.ok (turnContinue, _) = Except.ok (turnContinue, _)
  have suspended : w.suspended = [a] := pre.2.2
  have self : (a != a) = false := by
    rcases a with ⟨worker, pid, iterations⟩
    cases worker <;> change (!(pid == pid && iterations == iterations)) = false <;> simp
  simp [cookieActivationSnapshot, Campaign2.snapshot, Campaign2.core, detached, suspended, List.filter_cons, self]

end Leanux.Proofs.WG.Progress
