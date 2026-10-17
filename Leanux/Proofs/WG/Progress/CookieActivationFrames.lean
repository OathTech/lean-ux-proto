import Leanux.Proofs.WG.Progress.CookieActivationLoop
import Leanux.Proofs.WG.Progress.ScheduleTurn

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

theorem cookieActivation_snapshot (a : Activation) (w : World) (d : Device)
    (summary : CookieActivationSummary) :
    Campaign2.Product.snapshot (cookieActivationWorld a w d summary) =
      cookieActivationSnapshot a d (Campaign2.Product.snapshot w) summary := by
  rfl

theorem cookieDetached_snapshot (a : Activation) (w : World) :
    Campaign2.Product.snapshot (detached w a) =
      {Campaign2.Product.snapshot w with ambient := {(Campaign2.Product.snapshot w).ambient with
        suspended := w.ambient.suspended.filter (· != a)}} := by
  rfl


end Leanux.Proofs.WG.Progress
