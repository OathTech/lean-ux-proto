import Leanux.Proofs.WG.Progress.CookieActivationCompositionModel

/-! Historical drained prediction pending the physical-ring counterexample disposition. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress
open Leanux

theorem cookieActivationSnapshot_drained (a : Activation) (d : WG.Device)
    (entry : Campaign2.Snapshot) (summary : CookieActivationSummary)
    (processed : summary.processed = d.handshakeQueue.length) :
    (cookieActivationSnapshot a d entry summary).wg.device =
      some {d with handshakeQueue := [], handshakeQueueLen := d.handshakeQueueLen - summary.processed} := by
  simp [cookieActivationSnapshot, processed]

end Leanux.Proofs.WG.Progress
