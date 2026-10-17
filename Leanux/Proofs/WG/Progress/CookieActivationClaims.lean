import Leanux.Proofs.WG.Progress.CookieSchedulerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Correction of count-based drain adequacy: actual activation and bounded
hybrid execution have the same full Product outcome, including all failures. -/
theorem cookieActivation_outcome (a : Activation) (d : Device) (records : List HiddenRecord)
    (receive : a.worker = .receiveWorker) (table : d.indexTable = []) (cookies : CookieOnly d) :
    Campaign2.Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records)
      (Activation.run a) (cookieHybridRun a d.handshakeQueue.count) := by
  intro w pre
  rw [cookieActivation_run a w d records receive pre.1 table cookies pre.2]
  rfl

/-- Correction: resumption performs actual detachment and the bounded run.
It need not drain, yield after one item, or fail only with a hidden mismatch. -/
theorem cookieResumption_progress (a : Activation) (d : Device) (records : List HiddenRecord)
    (receive : a.worker = .receiveWorker) (table : d.indexTable = []) (cookies : CookieOnly d) :
    Campaign2.Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records)
      (resumeCandidates none [a]) (cookieBoundedResumption a d.handshakeQueue.count) := by
  intro w pre
  rw [resumeCandidates_singleton]
  have run := cookieActivation_run a (detached w a) d records receive pre.1 table cookies pre.2
  rw [run]
  rfl

/-- Correction: pure resolver success identifies the control branch only.
The original turn agrees exactly with the bounded probe and detached rerun;
no queue-drain, strict record-suffix or summary-faithfulness conclusion follows. -/
theorem cookieScheduler_progress (a : Activation) (d : Device) (records : List HiddenRecord)
    (summary : CookieActivationSummary) (receive : a.worker = .receiveWorker)
    (table : d.indexTable = []) (cookies : CookieOnly d)
    (resolve : resolveCookieActivation d.handshakeQueue.count records = .ok summary) :
    Campaign2.Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some records ∧ s.ambient.suspended = [a])
      (scheduleTurn none) (cookieBoundedScheduler a d.handshakeQueue.count) := by
  intro w pre
  rw [cookieScheduler_run a w d records summary receive pre.1 table cookies pre.2.1 pre.2.2 resolve]

end Leanux.Proofs.WG.Progress
