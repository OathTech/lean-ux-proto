import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchModel
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG
/-- Retain the actual inspection bit and the pending/inspection eligibility test. -/
def RetryQueueOutcome (pid : PeerId) (p : Peer) (seen : Option Bool) (out : Device) : Prop :=
  out.sendWorkQueue = [] ∨ (out.sendWorkQueue = [pid] ∧
    out.peers[pid]? = some {p with refcount := p.refcount + 1, handshakePending := true} ∧
    p.isDead = false ∧ 0 < p.refcount ∧
    ∃ queued, seen = some queued ∧ (p.handshakePending && !queued) = false)

/-- The actual inspection, rather than entry queue/pending coherence, explains eligibility. -/
def InspectedFreshRetryPeer (before queued : Peer) (seen : Option Bool) : Prop :=
  before.isDead = false ∧
  (∃ inspected, seen = some inspected ∧ (before.handshakePending && !inspected) = false) ∧
  0 < before.refcount ∧ queued.internalId = before.internalId ∧
  queued.timerHandshakeAttempts = before.timerHandshakeAttempts + 1 ∧
  queued.refcount = before.refcount + 1 ∧ queued.handshakePending = true ∧
  queued.timerRetransmitHandshake = none


end Leanux.Proofs.WG.TimerDiscipline
