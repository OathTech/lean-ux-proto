import Leanux.Proofs.WG.Progress.CookieScheduleOutcomeSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Progress

/-- The previous unconditional completion assertion is replaced by full Product
outcome agreement with the actual bounded first turn and unchanged remainder.
The entire original supplied-record and logical-membership domain remains. -/
theorem schedule_outcome (ys : List (List UInt8)) (a : Activation)
    (d : Device) (stop : List UInt8)
    (receive : a.worker = .receiveWorker) (table : d.indexTable = []) (cookies : CookieOnly d)
    (valid : ∀ bytes ∈ ys, bytes.length = 8) (stopLen : stop.length = 8)
    (occupancy : ys.length ≤ d.handshakeQueue.count) :
    Campaign2.Product.AgreesOn
      (fun s => s.wg.device = some d ∧ s.ambient.hidden = some (records ys stop) ∧ s.ambient.suspended = [a])
      (schedule none) (boundedSchedule a d.handshakeQueue.count (ys.length + 1)) := by
  intro w pre
  exact congrArg Campaign2.Product.observeResult
    (schedule_run ys a w d stop receive pre.1 table cookies pre.2.1 pre.2.2 valid stopLen occupancy)

end Leanux.Proofs.WG.Progress.CookieFull
