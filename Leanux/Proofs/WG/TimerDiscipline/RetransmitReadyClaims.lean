import Leanux.Proofs.WG.TimerDiscipline.RetransmitReadySource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2
/-- Total original hook under static supplied-record premises. The running/live
guard selects exact rearm or skip effects after the caller clock and jitter reads. -/
theorem retransmitHook_returns (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (valid : input.Valid) (entry : Snapshot) :
    Campaign2.Returns (timersHandshakeInitiated pid)
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.wg.armRecords = true ∧
        s.ambient.hidden = some (input.records rest))
      (fun _ final => final = if d.running && !p.isDead
        then retransmitReadyView entry d pid p input rest
        else retransmitSkippedView entry d input rest) := by
  intro actual pre
  obtain ⟨rfl, device, mode, records⟩ := pre
  cases guard : (d.running && !p.isDead) with
  | false =>
    refine ⟨(), _, retransmitSkipped_run pid d p input rest resident guard valid actual device mode records, ?_⟩
    simp only [Bool.false_eq_true, ite_false]
    rfl
  | true =>
    have both : d.running = true ∧ p.isDead = false := by simpa using guard
    refine ⟨(), _, retransmitReady_run pid d p input rest resident both.1 both.2 valid actual device mode records, ?_⟩
    simp only [ite_true]
    rfl

end Leanux.Proofs.WG.TimerDiscipline
