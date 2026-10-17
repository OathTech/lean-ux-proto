import Leanux.Proofs.WG.Progress.CookieScheduleModel
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Concrete transforms and their complete Product projection. These are data-only
frames, not assertions that a receive activation reaches either transform. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Proofs.WG.Progress

def finished (w : World) (d : Device) : World :=
  {w with
    wg := {w.wg with dev := some {d with
      handshakeQueue := cookieRingAfter d.handshakeQueue.count d.handshakeQueue
      handshakeQueueLen := d.handshakeQueueLen - d.handshakeQueue.count}}
    ambient := {w.ambient with
      hidden := some []
      suspended := []
      steps := (cookieProcessedSteps w.ambient.netRxSection d.handshakeQueue.count w.ambient.steps).push
        {decision := .workerConsumed, outcome := false, netRx := w.ambient.netRxSection}}}

def yieldedWorld (a : Activation) (w : World) (d : Device) (rs : List HiddenRecord) : World :=
  {w with
    wg := {w.wg with dev := some (cookieTailDevice d)}
    ambient := {w.ambient with
      hidden := some rs
      suspended := [{a with iterations := a.iterations + 1}]
      steps := cookiePacketSteps w.ambient.netRxSection w.ambient.steps}}

-- Retired as refuted, not type-given: final_composition recomputed a remaining
-- count after one consume. cookieBadTail_count_composition_false in
-- CookieScheduleSupportFindings disproves that equation on arbitrary metadata.

theorem finished_snapshot (w : World) (d : Device) :
    Campaign2.Product.snapshot (finished w d) =
      finishedSnapshot d (Campaign2.Product.snapshot w) := rfl

end Leanux.Proofs.WG.Progress.CookieFull
