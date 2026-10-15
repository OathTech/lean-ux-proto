import Leanux.Proofs.WG.TimerDiscipline.SendDispatchSource

set_option autoImplicit false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

theorem source_send_dispatch_path (d : Device) (units : List (Nat × Nat × Nat))
    (retained : RetainedSendQueue d) :
    Campaign2.Ensures (observed Env.runOneSendWorker sendWorkerExecution)
      (fun s => s.wg.device = some d ∧ s.ambient.unitPeers = units)
      (fun result final => ∃ execution, result.1 = .ok (execution, final) ∧
        CompletedSendWorker d units execution final) := by
  apply observed_effect
  intro w result final pre run
  cases result
  obtain ⟨execution, path⟩ := sendWorkerExecution_success w final run
  exact ⟨execution, observe_ok path,
    sendWorkerExecution_effect d units retained w execution final pre path⟩

theorem source_send_dispatch (d : Device) (retained : RetainedSendQueue d) :
    Campaign2.Ensures Env.runOneSendWorker (fun s => s.wg.device = some d)
      (fun _ final => ∃ pid p, pid ∈ d.sendWorkQueue ∧ d.peers[pid]? = some p ∧
        p.handshakePending = true ∧ workerObservation final pid =
          some (p.internalId, p.timerHandshakeAttempts, p.refcount - 1)) := by
  intro w result final pre run
  cases result
  obtain ⟨execution, path⟩ := sendWorkerExecution_success w final run
  have facts := sendWorkerExecution_effect d w.unitPeers retained
    w execution final ⟨pre, rfl⟩ path
  obtain ⟨selection, p, resident, pending, _, _, _, finalView⟩ := facts
  exact ⟨execution.pid, p, selection.1, resident, pending, finalView⟩

end Leanux.Proofs.WG.TimerDiscipline
