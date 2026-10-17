import Leanux.Proofs.WG.TimerDiscipline.RetryRearmModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2.Product

/-- One explicit selected wheel-unit/send pair, retaining its actual full observations. -/
structure RetrySequenceStep where
  unit : RetryUnit
  before : Snapshot
  result : RetryRearmObservation
  after : Snapshot

/-- Each exit is the next entry. The local certificate retains the supplied selected unit,
actual queue inspection, section observations, reference effects and conditional rearming.
This relation makes no claim about selection by the outer wheel scheduler. -/
inductive RetrySequenceChain : Snapshot → List RetryUnit → List RetrySequenceStep → Snapshot → Prop
  | nil (entry : Snapshot) : RetrySequenceChain entry [] [] entry
  | cons (step : RetrySequenceStep) (units : List RetryUnit)
      (rest : List RetrySequenceStep) (final : Snapshot) (d : Device)
      (device : step.before.wg.device = some d) (empty : d.sendWorkQueue = [])
      (certificate : RetryRearmCertificate d step.unit step.result step.after)
      (tail : RetrySequenceChain step.after units rest final) :
      RetrySequenceChain step.before (step.unit :: units) (step :: rest) final

/-- A condition on actual timer selections, not a request that those selections occur. -/
def SameRetryPeer (pid : PeerId) (steps : List RetrySequenceStep) : Prop :=
  ∀ step ∈ steps, ∃ selected,
    step.result.timer = .ok ((pid, .retransmitHandshake, selected), step.result.afterTimer)

def RetrySequenceCounts (pid : PeerId) (p : Peer) (units : List RetryUnit)
    (final : Snapshot) : Prop :=
  workerObservation final.toSnapshot pid =
    some (p.internalId, p.timerHandshakeAttempts + units.length, p.refcount) ∧
  (units ≠ [] → p.timerHandshakeAttempts + units.length ≤ MAX_TIMER_HANDSHAKES + 1 ∧
    (final.toSnapshot.peerAt pid).map Peer.handshakePending = some false)

/-- The empty sequence preserves its complete entry snapshot. Bounds and a
cleared pending flag require a nonempty sequence; entry attempts are unrestricted. -/
def RetrySequenceCertificate (d : Device) (units : List RetryUnit)
    (result : Snapshot × List RetrySequenceStep) (final : Snapshot) : Prop :=
  result.1.wg.device = some d ∧
  RetrySequenceChain result.1 units result.2 final ∧
  final.wg.device.map Device.sendWorkQueue = some [] ∧
  (units = [] → final = result.1) ∧
  ∀ pid p, d.peers[pid]? = some p → SameRetryPeer pid result.2 →
    RetrySequenceCounts pid p units final

end Leanux.Proofs.WG.TimerDiscipline
