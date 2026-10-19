import Leanux.Proofs.WG.Progress.InitiationCallerFiniteSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false

namespace Leanux.Proofs.WG.Progress.HandshakeFinite
open Leanux Leanux.WG

/-- Exact all-outcome agreement for the original initiation sender and its
finite source, without a successful-run or input-availability premise. -/
theorem original_sendInitiation_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.sendHandshakeInitiation pid)
      (sendInitiation pid) := by
  rw [sendInitiation_source]
  intro g ambient pre
  rfl

/-- The whole queued worker has the same complete outcome, including source
Stops in its sender or final release, as the concrete finite evaluator. -/
theorem original_sendWorker_finite (pid : PeerId) :
    Campaign2.AgreesOn (fun _ => True) (WG.handshakeSendWorker pid)
      (sendWorker pid) := by
  rw [sendWorker_source]
  intro g ambient pre
  rfl

end Leanux.Proofs.WG.Progress.HandshakeFinite
