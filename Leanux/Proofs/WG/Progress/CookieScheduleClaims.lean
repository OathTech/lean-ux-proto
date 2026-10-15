import Leanux.Proofs.WG.Progress.CookieScheduleSource

/-! Projected total-success contract for the full original scheduler in the explicit cookie-only receive domain. Other queues need not be empty; this is no claim of scheduler fairness. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Progress

theorem schedule_outcome (ys : List (List UInt8)) (a : Activation)
    (d : Device) (stop : List UInt8)
    (receive : a.worker = .receiveWorker) (table : d.indexTable = []) (cookies : CookieOnly d)
    (valid : ∀ bytes ∈ ys, bytes.length = 8) (stopLen : stop.length = 8)
    (occupancy : ys.length ≤ d.handshakeQueue.length) :
    Campaign2.Observes (schedule none)
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some (records ys stop) ∧
        s.ambient.suspended = [a])
      (fun entry outcome => outcome = .ok ((), finishedSnapshot d entry)) := by
  intro w pre
  have run := schedule_run ys a w d stop receive pre.1 table cookies pre.2.1 pre.2.2
    valid stopLen occupancy
  unfold Campaign2.observeResult
  rw [run]
  rfl

end Leanux.Proofs.WG.Progress.CookieFull
