import Leanux.Proofs.WG.Progress.CookieRingModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG

/-- Exact physical consumption model; no count-to-drain adequacy is asserted. -/
abbrev cookieActivationSnapshot := cookieRingActivationSnapshot
abbrev cookieTailDevice := cookieRingTailDevice
abbrev cookiePacketSnapshot := cookieRingPacketSnapshot

theorem cookieActivationSnapshot_continue (a : Activation) (d : Device)
    (entry : Campaign2.Product.Snapshot) (records : List HiddenRecord)
    (summary : CookieActivationSummary) :
    cookieActivationSnapshot {a with iterations := a.iterations + 1}
      (cookieTailDevice d) (cookiePacketSnapshot d entry records) summary =
    cookieActivationSnapshot a d entry {summary with processed := summary.processed + 1} :=
  cookieRingActivationSnapshot_continue a d entry records summary


end Leanux.Proofs.WG.Progress
