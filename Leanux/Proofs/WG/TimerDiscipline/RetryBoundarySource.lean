import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesSource
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- The native decision needs no timer-arm record or mode. -/
theorem retransmitDecision_above_limit (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts) :
    Campaign2.Returns (retransmitDecision pid) (fun s => s.wg.device = some d)
      (fun result s => result = true ∧ s.wg.device = some d) := by
  intro g ambient device
  let inputs := {ambient with steps := ambient.steps.push {
    decision := .retransmitGiveUp, outcome := true,
    operands := some (Int.ofNat p.timerHandshakeAttempts, Int.ofNat MAX_TIMER_HANDSHAKES),
    netRx := ambient.netRxSection}}
  refine ⟨true, g, inputs, ?_, rfl, device⟩
  change g.dev = some d at device
  simp [retransmitDecision, getPeer, getDev, device, resident, limit,
    branchCmp, AmbientM.branchCmp, inputs]
  rfl

/-- Keep the actual decision log and entire give-up tail, including failures. -/
theorem expiredRetransmit_forced_giveUp (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts) :
    Campaign2.AgreesOn (fun s => s.wg.device = some d)
      (expiredRetransmitHandshake pid)
      (do let _ ← retransmitDecision pid; retransmitGiveUp pid) := by
  intro g ambient pre
  obtain ⟨result, after, inputs, run, value, device⟩ :=
    retransmitDecision_above_limit pid d p resident limit g ambient pre
  subst result
  have equality : ((expiredRetransmitHandshake pid).run g).run ambient =
      ((do let _ ← retransmitDecision pid; retransmitGiveUp pid).run g).run ambient := by
    rw [retransmitDecision_source]
    change (((retransmitDecision pid).run g).run ambient >>= _) =
      (((retransmitDecision pid).run g).run ambient >>= _)
    rw [run]
    rfl
  exact congrArg Campaign2.observeResult equality

end Leanux.Proofs.WG.TimerDiscipline
