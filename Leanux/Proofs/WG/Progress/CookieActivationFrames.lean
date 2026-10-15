import Leanux.Proofs.WG.Progress.CookieActivationLoop
import Leanux.Proofs.WG.Progress.ScheduleTurn

/-! Projection and detachment equations, kept apart from the public operational claims. -/

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux

theorem cookieActivation_snapshot (a : Activation) (w : World) (d : WG.Device)
    (summary : CookieActivationSummary) :
    Campaign2.snapshot (cookieActivationWorld a w d summary) =
      cookieActivationSnapshot a d (Campaign2.snapshot w) summary := by
  rfl

theorem cookieDetached_snapshot (a : Activation) (w : World) :
    Campaign2.snapshot (detached w a) =
      {Campaign2.snapshot w with ambient := {(Campaign2.snapshot w).ambient with
        suspended := w.suspended.filter (· != a)}} := by
  rfl

end Leanux.Proofs.WG.Progress
