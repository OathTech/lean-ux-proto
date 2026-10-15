import Leanux.Proofs.WG.TimerDiscipline.RetryRearmModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- One original timer/send pair, with observations at its actual boundaries. -/
structure RetrySequenceStep where
  horizon : UInt64
  before : Snapshot
  result : RetryRearmObservation
  after : Snapshot

/-- Each exit is the next entry. The local certificate retains actual selection,
section observations, queue/reference effects and conditional recorded rearming. -/
inductive RetrySequenceChain : Snapshot → List UInt64 → List RetrySequenceStep → Snapshot → Prop
  | nil (entry : Snapshot) : RetrySequenceChain entry [] [] entry
  | cons (step : RetrySequenceStep) (horizons : List UInt64)
      (rest : List RetrySequenceStep) (final : Snapshot) (d : Device)
      (device : step.before.wg.device = some d) (empty : d.sendWorkQueue = [])
      (certificate : RetryRearmCertificate d step.horizon step.result step.after)
      (tail : RetrySequenceChain step.after horizons rest final) :
      RetrySequenceChain step.before (step.horizon :: horizons) (step :: rest) final

/-- A condition on actual timer selections, not a request that those selections occur. -/
def SameRetryPeer (pid : PeerId) (steps : List RetrySequenceStep) : Prop :=
  ∀ step ∈ steps, ∃ selected,
    step.result.timer = .ok ((pid, .retransmitHandshake, selected), step.result.afterTimer)

def RetrySequenceCounts (pid : PeerId) (p : Peer) (horizons : List UInt64)
    (final : Snapshot) : Prop :=
  workerObservation final pid =
    some (p.internalId, p.timerHandshakeAttempts + horizons.length, p.refcount) ∧
  (horizons ≠ [] → p.timerHandshakeAttempts + horizons.length ≤ MAX_TIMER_HANDSHAKES + 1 ∧
    (final.peerAt pid).map Peer.handshakePending = some false)

/-- The empty sequence preserves its complete entry snapshot. Bounds and a
cleared pending flag require a nonempty sequence; entry attempts are unrestricted. -/
def RetrySequenceCertificate (d : Device) (horizons : List UInt64)
    (result : Snapshot × List RetrySequenceStep) (final : Snapshot) : Prop :=
  result.1.wg.device = some d ∧
  RetrySequenceChain result.1 horizons result.2 final ∧
  final.wg.device.map Device.sendWorkQueue = some [] ∧
  (horizons = [] → final = result.1) ∧
  ∀ pid p, d.peers[pid]? = some p → SameRetryPeer pid result.2 →
    RetrySequenceCounts pid p horizons final

end Leanux.Proofs.WG.TimerDiscipline
