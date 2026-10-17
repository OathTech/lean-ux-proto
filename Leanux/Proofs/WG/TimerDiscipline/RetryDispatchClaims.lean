import Leanux.Proofs.WG.TimerDiscipline.RetryDispatchSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Exact successful retry-pair certificate for the supplied current wheel unit.
The original empty-queue domain is retained; eligibility and attempt bound are
derived from the actual callback inspection and following worker success. -/
theorem source_retry_dispatch (d : Device) (unit : RetryUnit)
    (empty : d.sendWorkQueue = []) :
    Campaign2.Product.Ensures (observedRetryDispatch unit)
      (fun s => s.wg.device = some d)
      (RetryDispatchCertificate d unit) := by
  intro initial result final device run
  rw [observedRetryDispatch_run] at run
  cases ht : (timerDispatchUnit_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run initial with
  | error e => rw [ht] at run; cases run
  | ok pair =>
    obtain ⟨u, afterTimer⟩ := pair
    cases u
    rw [ht] at run
    change (Env.runOneSendWorker.run afterTimer >>= fun sendOut =>
      Except.ok (RetryDispatchObservation.mk
        (Campaign2.Product.observeResult ((timerExecutionPath .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run initial))
        (Campaign2.Product.snapshot afterTimer)
        (Campaign2.Product.observeResult ((retryInspectionPath unit).run initial))
        (Campaign2.Product.observeResult (sendWorkerExecution.run afterTimer)), sendOut.2)) =
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
      rw [fireTimer_source, StateT.run_bind] at ht
      cases prefixRun : (timerDispatchPrefix_variant .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run initial with
      | error stop => rw [prefixRun] at ht; cases ht
      | ok pair =>
        obtain ⟨u, selected⟩ := pair
        cases u
        rw [prefixRun] at ht
        change (fireWheelSelected .timerRetransmit unit.pid .retransmitHandshake unit.wheel).run selected = .ok ((), afterTimer) at ht
        have selectedDevice : selected.wg.dev = some d :=
          (Noise.Product.ensures_iff _ _ _).mpr
            (timerSelection_kernel_spec (fun g _ _ _ => g.dev = some d)
              .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step)
            initial () selected device prefixRun
        have resident : ∃ p, d.peers[unit.pid]? = some p := by
          cases stored : d.peers[unit.pid]? with
          | some p => exact ⟨p, rfl⟩
          | none =>
            have deletion : (liftWG (delTimer unit.pid .retransmitHandshake)).run selected =
                .error (.invariant s!"dangling peer {unit.pid}") := by
              have native : ((delTimer unit.pid .retransmitHandshake).run selected.wg).run selected.ambient =
                  .error (.invariant s!"dangling peer {unit.pid}") := by
                simp [delTimer, getPeer, getDev, selectedDevice, stored,
                  Leanux.invariant, AmbientM.invariant]
                rfl
              change (((delTimer unit.pid .retransmitHandshake).run selected.wg).run selected.ambient >>= fun ((value,g),a) =>
                Except.ok (value, {selected with wg := g, ambient := a})) = _
              rw [native]
              rfl
            change ((liftWG (delTimer unit.pid .retransmitHandshake)).run selected >>= _) = _ at ht
            rw [deletion] at ht
            cases ht
        obtain ⟨p, stored⟩ := resident
        have erased : ((observedFireSelected unit.pid unit.wheel).run selected >>= fun out =>
            Except.ok ((), out.2)) = .ok ((), afterTimer) := by
          change (do let _ ← observedFireSelected unit.pid unit.wheel; pure ()).run selected = _
          rw [observedFireSelected_erase]
          exact ht
        cases seenRun : (observedFireSelected unit.pid unit.wheel).run selected with
        | error stop => rw [seenRun] at erased; cases erased
        | ok pair =>
          obtain ⟨seen, after⟩ := pair
          rw [seenRun] at erased
          have sameAfter : after = afterTimer := congrArg Prod.snd (Except.ok.inj erased)
          subst after
          have fullSeen : (retryInspectionPath unit).run initial = .ok (seen, afterTimer) := by
            simp only [retryInspectionPath, StateT.run_bind, prefixRun]
            exact seenRun
          have timerRun : (timerExecutionPath .timerRetransmit unit.pid .retransmitHandshake unit.wheel unit.step).run initial =
              .ok ((unit.pid, .retransmitHandshake, Campaign2.Product.snapshot selected), afterTimer) := by
            simp only [timerExecutionPath, StateT.run_bind, prefixRun]
            change ((fireWheelSelected .timerRetransmit unit.pid .retransmitHandshake unit.wheel).run selected >>= fun out =>
              Except.ok ((unit.pid, PeerTimer.retransmitHandshake, Campaign2.Product.snapshot selected), out.2)) = _
            rw [ht]
            rfl
          have limit := fireSelected_send_limit unit.pid unit.wheel d p stored empty selected afterTimer finish
            selectedDevice ht hw
          have facts := fireSelected_empty unit.pid unit.wheel d p stored empty limit
            selected seen afterTimer selectedDevice seenRun
          obtain ⟨send, sendRun, completed⟩ := retry_send_completed_inspected unit.pid p seen afterTimer finish facts hw
          exact ⟨Campaign2.Product.snapshot selected, send, p, seen,
            observe_ok timerRun, observe_ok fullSeen, observe_ok sendRun, selectedDevice, stored, limit, completed⟩

end Leanux.Proofs.WG.TimerDiscipline
