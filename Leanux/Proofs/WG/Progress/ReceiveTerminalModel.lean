import Leanux.WG.PtrRing
import Leanux.Proofs.WG.Progress.ActivationExitModel
import Leanux.Proofs.WG.Progress.RecordSuffixModel

/-! The final empty receive poll and its section-stop read, measured from the
actual entry of that final iteration. This does not describe earlier packet
iterations or assert that an activation completes. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux

def ReceiveTerminal (audit : ActivationExitAudit Campaign2.Product.Snapshot) : Prop :=
  match audit with
  | .ran _ _ _ (.ended _ _ before middle stop) =>
      (∃ d, before.wg.device = some d ∧ d.handshakeQueue.peek = none) ∧
      middle.wg = before.wg ∧ middle.ambient.hidden = before.ambient.hidden ∧
      ∀ records, before.ambient.hidden = some records →
        ∀ bytes final, stop = .ok (bytes,final) → StrictTail records final.ambient.hidden
  | _ => True

end Leanux.Proofs.WG.Progress.RecordSuffix
