import Leanux.Proofs.WG.TimerDiscipline.RetryEligibilityModel
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchModel
import Leanux.Proofs.WG.TimerDiscipline.SendView

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- Completion with eligibility witnessed by the actual callback inspection,
including the same reference, attempt, queue and pending effects. -/
def CompletedInspectedRetryDispatch (pid : PeerId) (before : Peer) (seen : Option Bool)
    (afterTimer : Campaign2.Product.Snapshot) (send : SendWorkerExecution)
    (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ d queued, afterTimer.wg.device = some d ∧ d.sendWorkQueue = [pid] ∧
    d.peers[pid]? = some queued ∧ InspectedFreshRetryPeer before queued seen ∧ send.pid = pid ∧
    CompletedSendWorker d afterTimer.ambient.unitPeers send final ∧
    workerObservation final.toSnapshot pid =
      some (before.internalId, before.timerHandshakeAttempts + 1, before.refcount) ∧
    workObservation final.toSnapshot pid = (some [], some false)

end Leanux.Proofs.WG.TimerDiscipline
