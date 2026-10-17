import Leanux.Proofs.WG.TimerDiscipline.RetryInspectedModel
import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchLeaves

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

theorem retry_send_completed_inspected (pid : PeerId) (before : Peer) (seen : Option Bool) (afterTimer final : World)
    (facts : ∃ d, afterTimer.wg.dev = some d ∧
      (d.sendWorkQueue = [] ∨ (d.sendWorkQueue = [pid] ∧
        ∃ queued, d.peers[pid]? = some queued ∧ InspectedFreshRetryPeer before queued seen)))
    (run : Env.runOneSendWorker.run afterTimer = .ok ((), final)) :
    ∃ send, sendWorkerExecution.run afterTimer = .ok (send, final) ∧
      CompletedInspectedRetryDispatch pid before seen (Campaign2.Product.snapshot afterTimer) send (Campaign2.Product.snapshot final) := by
  obtain ⟨d, device, queueCases⟩ := facts
  have nonempty := sendDispatch_nonempty d afterTimer () final device run
  rcases queueCases with empty | ⟨single, queued, resident, fresh⟩
  · exact False.elim (nonempty empty)
  · have retained : RetainedSendQueue d := by
      intro selected member peer same
      have selectedEq : selected = pid := by simpa [single] using member
      subst selected
      rw [resident] at same
      cases same
      have oldPositive := fresh.2.2.1
      have increment := fresh.2.2.2.2.2.1
      omega
    obtain ⟨send, execution⟩ := sendWorkerExecution_success afterTimer final run
    have completed := sendWorkerExecution_effect d afterTimer.ambient.unitPeers retained
      afterTimer send final ⟨device, rfl⟩ execution
    have selectedEq : send.pid = pid := by simpa [single] using completed.1.1
    have finalView := completed.2
    obtain ⟨actual, actualResident, _, _, _, _, view⟩ := finalView
    rw [selectedEq, resident] at actualResident
    cases actualResident
    have work := sendWorkerExecution_workView d afterTimer.ambient.unitPeers retained
      afterTimer send final ⟨device, rfl⟩ execution
    refine ⟨send, execution, d, queued, device, single, resident, fresh, selectedEq, completed, ?_, ?_⟩
    · rw [selectedEq] at view
      have identity := fresh.2.2.2.1
      have attempts := fresh.2.2.2.2.1
      have refs := fresh.2.2.2.2.2.1
      simpa [identity, attempts, refs] using view
    · simpa [selectedEq, single] using work


end Leanux.Proofs.WG.TimerDiscipline
