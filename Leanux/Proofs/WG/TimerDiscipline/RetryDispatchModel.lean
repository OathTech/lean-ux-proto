import Leanux.Proofs.WG.TimerDiscipline.RetryInspectedModel
import Leanux.Proofs.WG.TimerDiscipline.RetryUnitModel
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchModel
import Leanux.Proofs.WG.TimerDiscipline.SendView

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2
/-- Observations of the two original calls at their actual sequential entries. -/
structure RetryDispatchObservation where
  timer : Campaign2.Product.Outcome (PeerId × PeerTimer × Campaign2.Product.Snapshot)
  afterTimer : Campaign2.Product.Snapshot
  inspection : Campaign2.Product.Outcome (Option Bool)
  send : Campaign2.Product.Outcome SendWorkerExecution

/-- A freshly queued retry has one additional reference and a detached timer. -/
def FreshRetryPeer (before queued : Peer) : Prop :=
  before.isDead = false ∧ before.handshakePending = false ∧ 0 < before.refcount ∧
  queued.internalId = before.internalId ∧
  queued.timerHandshakeAttempts = before.timerHandshakeAttempts + 1 ∧
  queued.refcount = before.refcount + 1 ∧ queued.handshakePending = true ∧
  queued.timerRetransmitHandshake = none

/-- The retry worker consumes the freshly acquired reference, leaves the send
queue empty, and clears the selected pending flag. Retransmit rearming is separate. -/
def CompletedRetryDispatch (pid : PeerId) (before : Peer)
    (afterTimer : Campaign2.Product.Snapshot) (send : SendWorkerExecution) (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ d queued, afterTimer.wg.device = some d ∧ d.sendWorkQueue = [pid] ∧
    d.peers[pid]? = some queued ∧ FreshRetryPeer before queued ∧ send.pid = pid ∧
    CompletedSendWorker d afterTimer.ambient.unitPeers send final ∧
    workerObservation final.toSnapshot pid =
      some (before.internalId, before.timerHandshakeAttempts + 1, before.refcount) ∧
    workObservation final.toSnapshot pid = (some [], some false)

/-- A normal selected-unit pair exposes its actual resident and inspected
eligibility, deriving the attempt bound. No outer wheel-selection or logical
expiry condition is inferred from this explicitly supplied unit. -/
def RetryDispatchCertificate (d : Device) (unit : RetryUnit)
    (result : RetryDispatchObservation) (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ selected send p seen,
    result.timer = .ok ((unit.pid, .retransmitHandshake, selected), result.afterTimer) ∧
    result.inspection = .ok (seen, result.afterTimer) ∧
    result.send = .ok (send, final) ∧ selected.wg.device = some d ∧
    d.peers[unit.pid]? = some p ∧
    p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES ∧
    CompletedInspectedRetryDispatch unit.pid p seen result.afterTimer send final

end Leanux.Proofs.WG.TimerDiscipline
