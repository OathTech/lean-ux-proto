import Leanux.Proofs.WG.TimerDiscipline.PartialExchangeArmSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG

/-- Every actual realization of the full WG projection and arbitrary Ambient
in unrecorded timer-arm mode returns normally and arms zero-key without creating a session.
No prior history or runner reachability is asserted. -/
theorem giveUp_arms_without_session_creation :
    Campaign2.Returns (expiredRetransmitHandshake 0)
      (fun s => s.wg = partialExchangeArmView ∧ s.ambient.armRecords = false)
      (fun _ s => s.wg.keypairCounter = 0 ∧ s.wg.timerEnqueues = 1 ∧
        s.wg.device.map (fun d => d.keypairs.isEmpty) = some true ∧
        (s.peerAt 0).map
          (fun p => (p.handshakeState,p.keypairPrevious,p.keypairCurrent,p.keypairNext,p.timerZeroKeyMaterial)) =
          some (HANDSHAKE_CREATED_INITIATION,none,none,none,some ZERO_KEY_MATERIAL_TICKS.toUInt64)) := by
  intro g ambient pre
  obtain ⟨state,mode⟩ := pre
  have actual : g = partialExchangeArmState := by
    cases g
    cases state
    rfl
  subst g
  obtain ⟨final,run,counter,enqueues,keys,peer⟩ :=
    giveUp_arms_without_session_creation_run ambient mode
  exact ⟨(),final,partialExchangeArmAfter ambient,run,counter,enqueues,keys,peer⟩

end Leanux.Proofs.WG.TimerDiscipline
