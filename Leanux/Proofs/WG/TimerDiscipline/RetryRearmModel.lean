import Leanux.Proofs.WG.TimerDiscipline.SendRearmCertificateModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

structure RetryRearmObservation where
  timer : Outcome (PeerId × PeerTimer × Snapshot)
  afterTimer : Snapshot
  send : Outcome SendRearmExecution

def RetryRearmObservation.dispatch (result : RetryRearmObservation) : RetryDispatchObservation :=
  ⟨result.timer, result.afterTimer, result.send.map fun (send, final) => (send.send, final)⟩

/-- The existing retry certificate, including final queue/pending/ref facts,
is retained; only the original selected peer's conditional rearm is added. -/
def RetryRearmCertificate (d : Device) (horizon : UInt64)
    (result : RetryRearmObservation) (final : Snapshot) : Prop :=
  RetryDispatchCertificate d horizon result.dispatch final ∧
    ∃ send before, result.send = .ok (send, final) ∧
      d.peers[send.send.pid]? = some before ∧
      RearmCertificate send.send.pid
        (before.internalId, before.timerHandshakeAttempts + 1, before.refcount + 1, none)
        send.arm final

end Leanux.Proofs.WG.TimerDiscipline
