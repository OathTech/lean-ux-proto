import Leanux.Proofs.WG.TimerDiscipline.RetryBoundarySource
import Leanux.Proofs.WG.TimerDiscipline.TimerQueueFrames

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Std.Do

/-- Above the retry limit, normal callback completion leaves the send queue empty. -/
theorem expiredRetransmit_giveUp_empty (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (empty : d.sendWorkQueue = [])
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts) :
    Campaign2.Ensures (expiredRetransmitHandshake pid) (fun s => s.wg.device = some d)
      (fun _ s => s.wg.device.map Device.sendWorkQueue = some []) := by
  intro g ambient result final after pre run
  obtain ⟨value, next, inputs, decision, equal, device⟩ :=
    retransmitDecision_above_limit pid d p resident limit g ambient pre
  subst value
  rw [retransmitDecision_source] at run
  change (((retransmitDecision pid).run g).run ambient >>= _) = _ at run
  rw [decision] at run
  change ((retransmitGiveUp pid).run next).run inputs = _ at run
  change next.dev = some d at device
  exact (ensures_iff _ _ _).mpr (retransmitGiveUp_sendQueue pid (some []))
    next inputs result final after (by simp [device, empty]) run

end Leanux.Proofs.WG.TimerDiscipline
