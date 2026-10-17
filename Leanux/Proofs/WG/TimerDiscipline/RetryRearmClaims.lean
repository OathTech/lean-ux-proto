import Leanux.Proofs.WG.TimerDiscipline.SendRearmClaims
import Leanux.Proofs.WG.TimerDiscipline.RetryRearmSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Campaign2.Product Std.Do

/-- The supplied wheel unit's successful retry pair retains its inspected
eligibility and exact completion effects, plus conditional rearming of the same
selected peer. Outer wheel selection is a separate obligation. -/
theorem source_retry_rearm (d : Device) (unit : RetryUnit)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Product.Ensures (observedRetryRearm unit)
      (fun s => s.wg.device = some d) (RetryRearmCertificate d unit) := by
  intro initial result final device run
  have dispatchRun : (observedRetryDispatch unit).run initial = .ok (result.dispatch, final) := by
    rw [← observedRetryRearm_project]
    change ((observedRetryRearm unit).run initial >>= fun out => Except.ok (out.1.dispatch, out.2)) = _
    rw [run]; rfl
  have baseline := source_retry_dispatch d unit empty initial result.dispatch final device dispatchRun
  refine ⟨baseline, ?_⟩
  rw [observedRetryRearm_run] at run
  cases ht : (timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run initial with
  | error e => rw [ht] at run; cases run
  | ok pair =>
    obtain ⟨u, afterTimer⟩ := pair
    cases u
    rw [ht] at run
    change (Env.runOneSendWorker.run afterTimer >>= fun out => Except.ok
      (RetryRearmObservation.mk
        (observeResult ((timerExecutionPath .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run initial))
        (snapshot afterTimer) (observeResult ((retryInspectionPath unit).run initial))
        (observeResult (sendRearmExecution.run afterTimer)), out.2)) =
      .ok (result, final) at run
    cases hw : Env.runOneSendWorker.run afterTimer with
    | error e => rw [hw] at run; cases run
    | ok pair =>
      obtain ⟨u, finish⟩ := pair
      cases u
      rw [hw] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
      obtain ⟨send, sendRun⟩ := sendRearmExecution_success afterTimer finish hw
      obtain ⟨selected, oldSend, before, seen, timerObs, inspectionObs, sendObs, selectedDev,
        resident, limit, completed⟩ := baseline
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
        have pickedEq : picked = unit.pid := by simpa [queue] using member
        subst picked
        rw [queuedResident] at stored
        cases stored
        have positive := fresh.2.2.1
        have increment := fresh.2.2.2.2.2.1
        omega
      obtain ⟨actualPeer, actualResident, rearm⟩ := sendRearmExecution_effect queuedDev
        afterTimer.ambient.unitPeers retained afterTimer send finish ⟨afterDev, rfl⟩ sendRun
      rw [selectedPid, queuedResident] at actualResident
      cases actualResident
      refine ⟨send, before, observe_ok sendRun, ?_, ?_⟩
      · simpa [selectedPid] using resident
      · obtain ⟨alive, notPending, positive, identity, attempts, refs, pending, detached⟩ := fresh
        simpa [initiationView, identity, attempts, refs, detached] using rearm

end Leanux.Proofs.WG.TimerDiscipline
