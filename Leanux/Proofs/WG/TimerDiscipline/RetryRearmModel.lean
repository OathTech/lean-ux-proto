import Leanux.Proofs.WG.TimerDiscipline.SendRearmCertificateModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2.Product

structure RetryRearmObservation where
  timer : Outcome (PeerId × PeerTimer × Snapshot)
  afterTimer : Snapshot
  inspection : Outcome (Option Bool)
  send : Outcome SendRearmExecution

def RetryRearmObservation.dispatch (result : RetryRearmObservation) : RetryDispatchObservation :=
  ⟨result.timer, result.afterTimer, result.inspection, result.send.map fun (send, final) => (send.send, final)⟩

/-- The selected-unit retry certificate retains actual inspection and final queue,
pending and reference facts, together with conditional rearming of that same peer. -/
def RetryRearmCertificate (d : Device) (unit : RetryUnit)
    (result : RetryRearmObservation) (final : Snapshot) : Prop :=
  RetryDispatchCertificate d unit result.dispatch final ∧
    ∃ send before, result.send = .ok (send, final) ∧
      d.peers[send.send.pid]? = some before ∧
      RearmCertificate send.send.pid
        (before.internalId, before.timerHandshakeAttempts + 1, before.refcount + 1, none)
        send.arm final

end Leanux.Proofs.WG.TimerDiscipline
