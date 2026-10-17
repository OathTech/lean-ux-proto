import Leanux.Proofs.WG.TimerDiscipline.SendRearmModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchModel

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

structure RetryRearmObservation where
  timer : Outcome (PeerId × PeerTimer × Snapshot)
  afterTimer : Snapshot
  send : Outcome SendRearmExecution

def RetryRearmObservation.dispatch (result : RetryRearmObservation) : RetryDispatchObservation :=
  ⟨result.timer, result.afterTimer, result.send.map fun (send, final) => (send.send, final)⟩

def retransmitObservation (s : Snapshot) (pid : PeerId) : Option (Option UInt64) :=
  (s.peerAt pid).map Peer.timerRetransmitHandshake

/-- Normal sending exposes an actual prefix cut. Recorded rearming is
conditional on reaching the hook and on its actual device/peer/mode; the
caller/jitter path is asserted only in that branch. The clock gap is at send
return, while expiry is carried through release and section stop. -/
def RearmCertificate (pid : PeerId) (entry : InitiationView)
    (arm : InitiationRearmExecution) (final : Snapshot) : Prop :=
  ∃ reached beforeArm tail,
    arm.path = .ok ((reached, beforeArm, tail), beforeArm) ∧
    initiationObservation beforeArm pid = some entry ∧
    ∀ d p, beforeArm.wg.device = some d → d.peers[pid]? = some p →
      reached = true → d.running = true → p.isDead = false → beforeArm.wg.armRecords = true →
      ∃ caller afterRead jitter afterJitter,
        tail = .ok ((some caller, afterRead, jitter), afterJitter) ∧ jitter < HZ / 3 ∧
        arm.beforeRelease.peerAt pid = some (p.setTimer .retransmitHandshake
          (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧
        clockGap arm.beforeRelease caller ∧
        retransmitObservation final pid =
          some (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))

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
