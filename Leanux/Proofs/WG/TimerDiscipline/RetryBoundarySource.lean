import Leanux.Proofs.WG.TimerDiscipline.RetrySequenceClaims
import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesSource

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- The decision itself requires no timer-arm record or mode. -/
theorem retransmitDecision_above_limit (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts) :
    Returns (retransmitDecision pid) (fun w => w.k.wg = some d)
      (fun result w => result = true ∧ w.k.wg = some d) := by
  rw [returns_iff]
  mvcgen [retransmitDecision, getPeer, getDev, getK, invariant, branchCmp]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all

/-- Keep the original decision log and entire give-up tail, even if it fails. -/
theorem expiredRetransmit_forced_giveUp (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts) :
    Campaign2.AgreesOn (fun s => s.wg.device = some d)
      (expiredRetransmitHandshake pid)
      (do let _ ← retransmitDecision pid; retransmitGiveUp pid) := by
  intro entry pre
  obtain ⟨result, after, run, value, device⟩ :=
    retransmitDecision_above_limit pid d p resident limit entry pre
  subst result
  have equality : (expiredRetransmitHandshake pid).run entry =
      (do let _ ← retransmitDecision pid; retransmitGiveUp pid).run entry := by
    rw [retransmitDecision_source, StateT.run_bind, run, StateT.run_bind, run]
    rfl
  exact congrArg Campaign2.observeResult equality

end Leanux.Proofs.WG.TimerDiscipline
