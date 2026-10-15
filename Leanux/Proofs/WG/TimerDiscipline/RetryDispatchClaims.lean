import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchSource

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

theorem source_retry_dispatch (d : Device) (horizon : UInt64)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Ensures (observedRetryDispatch horizon)
      (fun s => s.wg.device = some d)
      (RetryDispatchCertificate d horizon) := by
  intro initial result final device run
  rw [observedRetryDispatch_run] at run
  cases ht : (Env.fireTimer .timerRetransmit horizon).run initial with
  | error e => rw [ht] at run; cases run
  | ok pair =>
    obtain ⟨u, afterTimer⟩ := pair
    cases u
    rw [ht] at run
    change (Env.runOneSendWorker.run afterTimer >>= fun sendOut =>
      Except.ok (RetryDispatchObservation.mk
        (observeResult ((timerExecutionPath .timerRetransmit horizon).run initial))
        (snapshot afterTimer) (observeResult (sendWorkerExecution.run afterTimer)), sendOut.2)) =
      Except.ok (result, final) at run
    cases hw : Env.runOneSendWorker.run afterTimer with
    | error e => rw [hw] at run; cases run
    | ok pair =>
      obtain ⟨u, finish⟩ := pair
      cases u
      rw [hw] at run
      obtain ⟨resultEq, finalEq⟩ := Prod.mk.inj (Except.ok.inj run)
      subst result
      subst final
      obtain ⟨pid, timer, selected, selection, callback, kind, selectedDevice, due⟩ :=
        fireTimer_execution .timerRetransmit horizon initial afterTimer d device ht
      have timerEq : timer = .retransmitHandshake := Option.some.inj kind.symm
      subst timer
      obtain ⟨listed, p, expiry, resident, armed, beforeHorizon⟩ := due
      obtain ⟨send, sendRun⟩ := sendWorkerExecution_success afterTimer finish hw
      have timerRun : (timerExecutionPath .timerRetransmit horizon).run initial =
          .ok ((pid, .retransmitHandshake, snapshot selected), afterTimer) := by
        simp only [timerExecutionPath, StateT.run_bind, selection]
        change ((fireSelected .timerRetransmit pid .retransmitHandshake).run selected >>= fun out =>
          Except.ok ((pid, PeerTimer.retransmitHandshake, snapshot selected), out.2)) = _
        rw [callback]
        rfl
      refine ⟨pid, snapshot selected, send, p, expiry, observe_ok timerRun,
        observe_ok sendRun, selectedDevice, listed, resident, armed, beforeHorizon, ?_⟩
      have limit := fireSelected_send_limit pid d p resident empty selected afterTimer finish
        selectedDevice callback hw
      refine ⟨limit, ?_⟩
      have facts := fireSelected_empty pid d p resident empty limit selected () afterTimer selectedDevice callback
      obtain ⟨actualSend, actualRun, completed⟩ := retry_send_completed pid p afterTimer finish facts hw
      rw [sendRun] at actualRun
      have sameSend : send = actualSend := congrArg Prod.fst (Except.ok.inj actualRun)
      subst actualSend
      exact completed

end Leanux.Proofs.WG.TimerDiscipline
