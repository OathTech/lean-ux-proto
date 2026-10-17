import Leanux.Proofs.WG.TimerDiscipline.AbsentGiveUpSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Historical name retained for audit continuity. The false total-return
claim is replaced by exact outcome agreement, including missing records and
all current wheel guards, over every original full Product realization. -/
theorem absentGiveUp_returns (pid : PeerId) (d : Device) (p : Peer)
    (input : GiveUpArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (absent : p.timerZeroKeyMaterial = none)
    (running : d.running = true) (alive : p.isDead = false)
    (valid : input.Valid) (entry : Product.Snapshot) :
    Product.AgreesOn
      (fun s => s = entry ∧ s.wg.device = some d ∧ s.ambient.armRecords = true ∧
        s.ambient.hidden = some (input.records rest))
      (liftWG (expiredRetransmitHandshake pid))
      (absentGiveUpArmContinuation pid d p input rest) := by
  intro actual pre
  obtain ⟨_, device, mode, records⟩ := pre
  apply congrArg Product.observeResult
  exact absentGiveUp_run pid d p input rest resident limit absent running alive
    valid actual device mode records

end Leanux.Proofs.WG.TimerDiscipline
