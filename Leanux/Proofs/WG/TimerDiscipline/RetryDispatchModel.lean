import Leanux.Proofs.WG.TimerDiscipline.SendDispatchModel
import Leanux.Proofs.WG.TimerDiscipline.SendView

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Observations of the two original calls at their actual sequential entries. -/
structure RetryDispatchObservation where
  timer : Outcome (PeerId × PeerTimer × Snapshot)
  afterTimer : Snapshot
  send : Outcome SendWorkerExecution

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
    (afterTimer : Snapshot) (send : SendWorkerExecution) (final : Snapshot) : Prop :=
  ∃ d queued, afterTimer.wg.device = some d ∧ d.sendWorkQueue = [pid] ∧
    d.peers[pid]? = some queued ∧ FreshRetryPeer before queued ∧ send.pid = pid ∧
    CompletedSendWorker d afterTimer.ambient.unitPeers send final ∧
    workerObservation final pid =
      some (before.internalId, before.timerHandshakeAttempts + 1, before.refcount) ∧
    workObservation final pid = (some [], some false)

/-- A normal pair exposes its selected resident peer and derives its entry
attempt bound, without an assumed output-reference invariant. -/
def RetryDispatchCertificate (d : Device) (horizon : UInt64)
    (result : RetryDispatchObservation) (final : Snapshot) : Prop :=
  ∃ pid selected send p expiry,
    result.timer = .ok ((pid, .retransmitHandshake, selected), result.afterTimer) ∧
    result.send = .ok (send, final) ∧ selected.wg.device = some d ∧
    pid ∈ d.peerList ∧ d.peers[pid]? = some p ∧
    p.timerRetransmitHandshake = some expiry ∧ timeBefore expiry horizon = true ∧
    p.timerHandshakeAttempts ≤ MAX_TIMER_HANDSHAKES ∧
    CompletedRetryDispatch pid p result.afterTimer send final

end Leanux.Proofs.WG.TimerDiscipline
