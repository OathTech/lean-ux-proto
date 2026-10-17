import Leanux.Proofs.WG.Progress.CookieActivationModel
import Leanux.Proofs.WG.Progress.CookieScheduleControlModel

/-! A data-only completion-shaped transform. It performs the initial count of
physical consumes, retaining slots and cursors; it does not assert that an actual
activation succeeds or that the resulting physical ring is empty. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Proofs.WG.Progress

def finishedSnapshot (d : Device) (entry : Campaign2.Product.Snapshot) : Campaign2.Product.Snapshot :=
  {entry with
    wg := {entry.wg with device := some {d with
      handshakeQueue := cookieRingAfter d.handshakeQueue.count d.handshakeQueue
      handshakeQueueLen := d.handshakeQueueLen - d.handshakeQueue.count}}
    ambient := {entry.ambient with
      hidden := some []
      suspended := []
      steps := (cookieProcessedSteps entry.ambient.netRxSection d.handshakeQueue.count
        entry.ambient.steps).push {decision := .workerConsumed, outcome := false, netRx := entry.ambient.netRxSection}}}

end Leanux.Proofs.WG.Progress.CookieFull
