import Leanux.Proofs.WG.Progress.CookieActivationModel
import Leanux.Proofs.WG.Progress.CookieScheduleControlModel

/-! The supplied record stream and final projected state for a complete cookie-only receive schedule. Each reschedule and final stop carries an arbitrary eight-byte payload. No ambient records or trailing records are included. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Progress

def finishedSnapshot (d : Device) (entry : Campaign2.Snapshot) : Campaign2.Snapshot :=
  {entry with
    wg := {entry.wg with device := some {d with
      handshakeQueue := []
      handshakeQueueLen := d.handshakeQueueLen-d.handshakeQueue.length}}
    ambient := {entry.ambient with
      hidden := some []
      suspended := []
      steps := (cookieProcessedSteps entry.ambient.netRxSection d.handshakeQueue.length
        entry.ambient.steps).push {decision := .workerConsumed, outcome := false, netRx := entry.ambient.netRxSection}}}

end Leanux.Proofs.WG.Progress.CookieFull
