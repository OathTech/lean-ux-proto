import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchModel
import Leanux.Proofs.WG.TimerDiscipline.RetrySource
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchClaims
import Leanux.Proofs.WG.TimerDiscipline.SendDispatchWorkSource

/-! Reference positivity and conditional completion retain their original domains. The stronger pending=false assumption remains explicit in FreshRetryPeer; this file does not derive it from an empty queue. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do
theorem sendDispatch_nonempty (d : Device) :
    Product.Ensures Env.runOneSendWorker (fun w => w.wg.dev = some d)
      (fun _ _ => d.sendWorkQueue ≠ []) := by
  intro w result final pre run
  rw [runOneSendWorker_source, StateT.run_bind] at run
  cases hs : sendWorkerSelection.run w with
  | error e => rw [hs] at run; cases run
  | ok pair =>
    obtain ⟨selected, after⟩ := pair
    have effect := sendWorkerSelection_effect d w.ambient.unitPeers w selected after ⟨pre, rfl⟩ hs
    intro empty
    have member := effect.2.2.1
    simp [empty] at member

/-- Normal worker selection eliminates the callback's empty-queue alternatives.
Only then is the retained-worker contract applied. -/
theorem retry_send_completed (pid : PeerId) (before : Peer) (afterTimer final : World)
    (facts : ∃ d, afterTimer.wg.dev = some d ∧
      (d.sendWorkQueue = [] ∨ (d.sendWorkQueue = [pid] ∧
        ∃ queued, d.peers[pid]? = some queued ∧ FreshRetryPeer before queued)))
    (run : Env.runOneSendWorker.run afterTimer = .ok ((), final)) :
    ∃ send, sendWorkerExecution.run afterTimer = .ok (send, final) ∧
      CompletedRetryDispatch pid before (Campaign2.Product.snapshot afterTimer) send (Campaign2.Product.snapshot final) := by
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


theorem queuedAfterClock_positive (pid : PeerId) (d : Device) (p : Peer) (now : Int64)
    (resident : d.peers[pid]? = some p)
    (expired : p.lastSentHandshake + REKEY_TIMEOUT.toInt64 * NSEC_PER_SEC64 ≤ now)
    (alive : p.isDead = false) :
    Ensures (queuedAfterClock pid p now) (fun g => g.dev = some d)
      (fun _ _ => 0 < p.refcount) := by
  intro g ambient result final after device run
  by_cases positive : 0 < p.refcount
  · exact positive
  have zero : p.refcount = 0 := by omega
  simp [queuedAfterClock, expired, alive, peerGet, requireNotPending, refcountInc,
    branch, branchCmp, AmbientM.branch, AmbientM.branchCmp,
    getPeer, getDev, device, resident, zero, unsupported, AmbientM.unsupported] at run
  cases run

end Leanux.Proofs.WG.TimerDiscipline
