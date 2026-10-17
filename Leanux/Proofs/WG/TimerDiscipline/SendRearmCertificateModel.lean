import Leanux.Proofs.WG.TimerDiscipline.SendRearmModel
import Leanux.Proofs.WG.TimerDiscipline.RecordedSiteSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Campaign2 Std.Do

def retransmitObservation (s : Campaign2.Snapshot) (pid : PeerId) : Option (Option UInt64) :=
  (s.peerAt pid).map Peer.timerRetransmitHandshake

/-- The actual arm includes its full wheel effect; the original clock gap and
final raw expiry survive the worker release and section-stop read. -/
def RearmCertificate (pid : PeerId) (entry : InitiationView)
    (arm : InitiationRearmExecution) (final : Campaign2.Product.Snapshot) : Prop :=
  ∃ reached beforeArm tail,
    arm.path = .ok ((reached, beforeArm, tail), beforeArm) ∧
    initiationObservation beforeArm.toSnapshot pid = some entry ∧
    ∀ d p, beforeArm.wg.device = some d → d.peers[pid]? = some p →
      reached = true → d.running = true → p.isDead = false → beforeArm.ambient.armRecords = true →
      ∃ caller afterRead jitter afterJitter,
        tail = .ok ((some caller, afterRead, jitter), afterJitter) ∧ jitter < HZ / 3 ∧
        recordedTimerEffect beforeArm.wg pid p .retransmitHandshake
          (REKEY_TIMEOUT_TICKS + jitter) caller arm.beforeRelease.wg ∧
        clockGap arm.beforeRelease.toSnapshot caller ∧
        retransmitObservation final.toSnapshot pid =
          some (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64))

end Leanux.Proofs.WG.TimerDiscipline
