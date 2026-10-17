import Leanux.Proofs.WG.TimerDiscipline.RetransmitReadySource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The checked caller/jitter prefix updates the actual Product input. The
original running/live guard then selects the exact log and actual arm action;
no Product component is reconstructed from the projected entry. -/
def retransmitHookContinuation (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord) : Leanux.M Unit := do
  modify fun initial => {initial with ambient := {initial.ambient with
    hidden := some ({site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest)
    steps := if d.running && !p.isDead then
      retransmitReadySteps initial.ambient.netRxSection initial.ambient.steps
      else retransmitSkippedSteps d.running initial.ambient.netRxSection initial.ambient.steps}}
  if d.running && !p.isDead then
    liftWG (armTimer pid .retransmitHandshake input.delay (some input.caller))

/-- Historical name retained for audit continuity. The original supplied-record
domain gives exact outcome agreement: inactive hooks return after the checked
caller/jitter prefix, while active hooks retain the actual arm's wheel errors.
The former unconditional-success conclusion omitted those required records. -/
theorem retransmitHook_returns (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (valid : input.Valid) (entry : Product.Snapshot) :
    Product.AgreesOn
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true ∧
        s.ambient.hidden = some (input.records rest))
      (liftWG (timersHandshakeInitiated pid))
      (retransmitHookContinuation pid d p input rest) := by
  intro actual pre
  obtain ⟨_, device, mode, records⟩ := pre
  apply congrArg Product.observeResult
  cases guard : (d.running && !p.isDead) with
  | false =>
    rw [retransmitSkipped_run pid d p input rest resident guard valid actual device mode records]
    simp [retransmitHookContinuation, guard]
    rfl
  | true =>
    have both : d.running = true ∧ p.isDead = false := by simpa using guard
    simpa [retransmitHookContinuation, guard] using
      retransmitReady_run pid d p input rest resident both.1 both.2 valid actual device mode records

end Leanux.Proofs.WG.TimerDiscipline
