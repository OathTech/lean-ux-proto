import Leanux.Proofs.WG.TimerDiscipline.SendRearmClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryRearmSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Campaign2 Std.Do

theorem source_retry_rearm (d : Device) (horizon : UInt64)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Ensures (observedRetryRearm horizon)
      (fun s => s.wg.device = some d) (RetryRearmCertificate d horizon) := by
  intro initial result final device run
  have dispatchRun : (observedRetryDispatch horizon).run initial = .ok (result.dispatch, final) := by
    rw [← observedRetryRearm_project]
    change ((observedRetryRearm horizon).run initial >>= fun out => Except.ok (out.1.dispatch, out.2)) = _
    rw [run]; rfl
  have baseline := source_retry_dispatch d horizon empty initial result.dispatch final device dispatchRun
  refine ⟨baseline, ?_⟩
  rw [observedRetryRearm_run] at run
  cases ht : (Env.fireTimer .timerRetransmit horizon).run initial with
  | error e => rw [ht] at run; cases run
  | ok pair =>
    obtain ⟨u, afterTimer⟩ := pair
    cases u
    rw [ht] at run
    change (Env.runOneSendWorker.run afterTimer >>= fun out => Except.ok
      (RetryRearmObservation.mk
        (observeResult ((timerExecutionPath .timerRetransmit horizon).run initial))
        (snapshot afterTimer) (observeResult (sendRearmExecution.run afterTimer)), out.2)) =
      .ok (result, final) at run
    cases hw : Env.runOneSendWorker.run afterTimer with
    | error e => rw [hw] at run; cases run
    | ok pair =>
      obtain ⟨u, finish⟩ := pair
      cases u
      rw [hw] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
      obtain ⟨send, sendRun⟩ := sendRearmExecution_success afterTimer finish hw
      obtain ⟨pid, selected, oldSend, before, expiry, timerObs, sendObs, selectedDev,
        listed, resident, armed, due, limit, completed⟩ := baseline
      have sameSend : send.send = oldSend := by
        change (observeResult (sendRearmExecution.run afterTimer)).map
          (fun (out, final) => (out.send, final)) = .ok (oldSend, snapshot finish) at sendObs
        rw [observe_ok sendRun] at sendObs
        exact congrArg Prod.fst (Except.ok.inj sendObs)
      subst oldSend
      obtain ⟨queuedDev, queued, afterDev, queue, queuedResident, fresh, selectedPid,
        worker, finalWorker, finalWork⟩ := completed
      have retained : RetainedSendQueue queuedDev := by
        intro picked member p stored
        have pickedEq : picked = pid := by simpa [queue] using member
        subst picked
        rw [queuedResident] at stored
        cases stored
        have positive := fresh.2.2.1
        have increment := fresh.2.2.2.2.2.1
        omega
      obtain ⟨actualPeer, actualResident, rearm⟩ := sendRearmExecution_effect queuedDev
        afterTimer.unitPeers retained afterTimer send finish ⟨afterDev, rfl⟩ sendRun
      rw [selectedPid, queuedResident] at actualResident
      cases actualResident
      refine ⟨send, before, observe_ok sendRun, ?_, ?_⟩
      · simpa [selectedPid] using resident
      · obtain ⟨alive, notPending, positive, identity, attempts, refs, pending, detached⟩ := fresh
        simpa [initiationView, identity, attempts, refs, detached] using rearm

end Leanux.Proofs.WG.TimerDiscipline
