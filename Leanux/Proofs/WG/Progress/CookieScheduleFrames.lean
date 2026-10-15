import Leanux.Proofs.WG.Progress.CookieScheduleModel
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Concrete state updates and composition/projection equations for the cookie-only schedule. These frame facts are separate from original execution and public claims. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.CookieFull
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.WG.Progress

def finished (w : World) (d : Device) : World :=
  {w with
    k := {w.k with wg := some {d with handshakeQueue := [], handshakeQueueLen := d.handshakeQueueLen-d.handshakeQueue.length}}
    hidden := some []
    suspended := []
    steps := (cookieProcessedSteps w.netRxSection d.handshakeQueue.length w.steps).push
      {decision := .workerConsumed, outcome := false, netRx := w.netRxSection}}
def yieldedWorld (a : Activation) (w : World) (d : Device) (rs : List HiddenRecord) : World :=
  {w with
    k := {w.k with wg := some (cookieTailDevice d)}
    hidden := some rs
    suspended := [{a with iterations := a.iterations+1}]
    steps := cookiePacketSteps w.netRxSection w.steps}
theorem final_composition (a : Activation) (w : World) (d : Device) (rs : List HiddenRecord)
    (nonempty : d.handshakeQueue ≠ []) :
    finished (yieldedWorld a w d rs) (cookieTailDevice d) = finished w d := by
  cases queue : d.handshakeQueue with
  | nil => exact False.elim (nonempty queue)
  | cons head tail =>
    simp [finished, yieldedWorld, cookieTailDevice, queue, cookieProcessedSteps,
      Nat.sub_sub, Nat.add_comm]
theorem finished_snapshot (w : World) (d : Device) :
    Campaign2.snapshot (finished w d) = finishedSnapshot d (Campaign2.snapshot w) := rfl

end Leanux.Proofs.WG.Progress.CookieFull
