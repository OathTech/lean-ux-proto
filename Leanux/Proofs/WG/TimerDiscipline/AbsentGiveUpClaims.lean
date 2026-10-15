import Leanux.Proofs.WG.TimerDiscipline.AbsentGiveUpSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- The exact source equality gives total return over every realization of
these projected entry facts and statically valid supplied records. -/
theorem absentGiveUp_returns (pid : PeerId) (d : Device) (p : Peer)
    (input : GiveUpArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (absent : p.timerZeroKeyMaterial = none)
    (running : d.running = true) (alive : p.isDead = false)
    (valid : input.Valid) (entry : Snapshot) :
    Campaign2.Returns (expiredRetransmitHandshake pid)
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.wg.armRecords = true ∧
        s.ambient.hidden = some (input.records rest))
      (fun _ final => final = absentGiveUpView entry d pid p input rest) := by
  intro actual pre
  obtain ⟨rfl, device, mode, records⟩ := pre
  refine ⟨(), _, absentGiveUp_run pid d p input rest resident limit absent running alive
    valid actual device mode records, ?_⟩
  rfl

end Leanux.Proofs.WG.TimerDiscipline
