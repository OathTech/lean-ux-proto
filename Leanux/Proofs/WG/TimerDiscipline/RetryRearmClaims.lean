import Leanux.Proofs.WG.TimerDiscipline.RetryRearmSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Campaign2 Std.Do

theorem initiationRearmExecution_effect (pid : PeerId) (entry : InitiationView) :
    Noise.Ensures (initiationRearmExecution pid)
      (fun w => initiationAt w pid = some entry)
      (fun arm final => RearmCertificate pid entry arm (snapshot final)) := by
  intro initial arm final pre run
  rw [initiationRearmExecution_run] at run
  cases hs : (sendHandshakeInitiation pid).run initial with
  | error e => rw [hs] at run; cases run
  | ok pair =>
    obtain ⟨u, beforeRelease⟩ := pair
    cases u
    rw [hs] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    obtain ⟨reached, beforeArm, prefixRun, finish⟩ :=
      source_initiation_arm_path pid initial beforeRelease hs
    have preserved := (ensures_iff _ _ _).mpr (initiationArmPrefix_view pid entry)
      initial reached beforeArm pre prefixRun
    refine ⟨reached, snapshot beforeArm,
      observeResult ((clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter).run beforeArm),
      ?_, preserved, ?_⟩
    · exact observe_ok (prefixInspect_run _ _ initial beforeArm reached prefixRun)
    · intro d p device resident reaches running alive records
      subst reached
      obtain ⟨caller, afterRead, jitter, afterJitter, read, draw, bounded, peer, gap⟩ :=
        source_initiation_send_arm pid d p resident running alive initial beforeArm beforeRelease
          prefixRun device records hs
      refine ⟨caller, snapshot afterRead, jitter, snapshot afterJitter,
        observe_ok (clockJitterPath_run _ _ _ _ _ _ _ read draw), bounded, peer, gap, ?_⟩
      change (peerAt beforeRelease pid).map Peer.timerRetransmitHandshake = _
      rw [peer]
      rfl

theorem rearmWorkerBody_effect (pid : PeerId) (entry : InitiationView)
    (retained : 1 < entry.2.2.1) :
    Noise.Ensures (rearmWorkerBody pid)
      (fun w => initiationAt w pid = some entry)
      (fun arm final => RearmCertificate pid entry arm (snapshot final)) := by
  intro initial arm final pre run
  simp only [rearmWorkerBody, StateT.run_bind] at run
  cases hi : (initiationRearmExecution pid).run initial with
  | error e => rw [hi] at run; cases run
  | ok pair =>
    obtain ⟨observedArm, beforeRelease⟩ := pair
    rw [hi] at run
    change ((peerPut (some pid)).run beforeRelease >>= fun out =>
      Except.ok (observedArm, out.2)) = .ok (arm, final) at run
    cases hp : (peerPut (some pid)).run beforeRelease with
    | error e => rw [hp] at run; cases run
    | ok pair =>
      obtain ⟨u, afterRelease⟩ := pair
      rw [hp] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
      have sendRun : (sendHandshakeInitiation pid).run initial = .ok ((), beforeRelease) := by
        rw [← initiationRearmExecution_erase]
        change ((initiationRearmExecution pid).run initial >>= fun out => Except.ok ((), out.2)) = _
        rw [hi]; rfl
      have held := sendHandshakeInitiation_workerView pid (initiationWorkerView entry)
        initial () beforeRelease (workerAt_of_initiationAt initial pid entry pre) sendRun
      obtain ⟨reached, beforeArm, tail, path, atArm, conditional⟩ :=
        initiationRearmExecution_effect pid entry initial observedArm beforeRelease pre hi
      refine ⟨reached, beforeArm, tail, path, atArm, ?_⟩
      intro d p device resident reaches running alive records
      obtain ⟨caller, afterRead, jitter, afterJitter, actual, bound, peer, gap, expiry⟩ :=
        conditional d p device resident reaches running alive records
      refine ⟨caller, afterRead, jitter, afterJitter, actual, bound, peer, gap, ?_⟩
      exact retained_peerPut_workerView_retransmit_variant pid entry.1 entry.2.1 entry.2.2.1
        _ retained beforeRelease u afterRelease ⟨held, expiry⟩ hp

theorem sendRearmExecution_effect (d : Device) (units : List (Nat × Nat × Nat))
    (retained : RetainedSendQueue d) :
    Campaign2.Ensures sendRearmExecution
      (fun s => s.wg.device = some d ∧ s.ambient.unitPeers = units)
      (fun execution final => ∃ p, d.peers[execution.send.pid]? = some p ∧
        RearmCertificate execution.send.pid (initiationView p) execution.arm final) := by
  intro w execution final pre run
  change (sendWorkerSelection.run w >>= fun sel =>
    (sendWorkerDequeue sel.1.2).run sel.2 >>= fun deq =>
    (hidden (.sectionStart .sendWorker)).run deq.2 >>= fun start =>
    (rearmWorkerBody sel.1.2).run start.2 >>= fun body =>
    (hidden (.sectionStop .sendWorker)).run body.2 >>= fun stop =>
    Except.ok (SendRearmExecution.mk (SendWorkerExecution.mk sel.1.1 sel.1.2 (snapshot deq.2)
      start.1 (snapshot start.2) (snapshot body.2) stop.1) body.1, stop.2)) =
      .ok (execution, final) at run
  cases hs : sendWorkerSelection.run w with
  | error e => simp only [hs, Bind.bind, Except.bind] at run; cases run
  | ok pair =>
    obtain ⟨selected, afterSelection⟩ := pair
    simp only [hs, Bind.bind, Except.bind] at run
    cases hd : (sendWorkerDequeue selected.2).run afterSelection with
    | error e => simp only [hd] at run; cases run
    | ok pair =>
      obtain ⟨u, beforeSection⟩ := pair
      simp only [hd] at run
      cases hb : (hidden (.sectionStart .sendWorker)).run beforeSection with
      | error e => simp only [hb] at run; cases run
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        simp only [hb] at run
        cases hw : (rearmWorkerBody selected.2).run afterStart with
        | error e => simp only [hw] at run; cases run
        | ok pair =>
          obtain ⟨arm, afterBody⟩ := pair
          simp only [hw] at run
          cases he : (hidden (.sectionStop .sendWorker)).run afterBody with
          | error e => simp only [he] at run; cases run
          | ok pair =>
            obtain ⟨stopBytes, afterStop⟩ := pair
            simp only [he] at run
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
            have selection := sendWorkerSelection_effect d units w selected afterSelection pre hs
            obtain ⟨p, resident, pending, deq⟩ :=
              sendWorkerDequeue_effect selected.2 d afterSelection _ beforeSection selection.1 hd
            have start := (ensures_iff _ _ _).mpr
              (hidden_kernel_spec (fun k => k.wg = some (dequeuedSendDevice d selected.2 p))
                (.sectionStart .sendWorker)) beforeSection bytes afterStart deq hb
            have bodyPre : initiationAt afterStart selected.2 = some (initiationView p) := by
              simp [initiationAt, peerAt, start, dequeuedSendDevice, initiationView]
            have body := rearmWorkerBody_effect selected.2 (initiationView p)
              (retained selected.2 selection.2.2.1 p resident) afterStart arm afterBody bodyPre hw
            obtain ⟨reached, beforeArm, tail, path, atArm, conditional⟩ := body
            refine ⟨p, resident, reached, beforeArm, tail, path, atArm, ?_⟩
            intro armDev armPeer device stored reaches running alive records
            obtain ⟨caller, afterRead, jitter, afterJitter, actual, bound, peer, gap, expiry⟩ :=
              conditional armDev armPeer device stored reaches running alive records
            refine ⟨caller, afterRead, jitter, afterJitter, actual, bound, peer, gap, ?_⟩
            exact (ensures_iff _ _ _).mpr
              (hidden_kernel_spec (fun k =>
                ((k.wg.bind fun d => d.peers[selected.2]?).map Peer.timerRetransmitHandshake) =
                  some (some (caller + (REKEY_TIMEOUT_TICKS + jitter).toUInt64)))
                (.sectionStop .sendWorker)) afterBody stopBytes afterStop expiry he

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
