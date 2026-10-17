import Leanux.Proofs.WG.TimerDiscipline.SendRearmCertificateModel
import Leanux.Proofs.WG.TimerDiscipline.SendRearmSource
import Leanux.Proofs.WG.TimerDiscipline.RetryRearmFrames
import Leanux.Proofs.WG.TimerDiscipline.RecordedSourceClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Noise Campaign2 Std.Do

private theorem recordedRetransmit_observations (pid : PeerId) (p : Peer)
    (before final : Campaign2.Snapshot) (d : Device) (delay : Nat) (caller : UInt64)
    (device : before.wg.device = some d) (resident : d.peers[pid]? = some p)
    (effect : recordedTimerEffect before.wg pid p .retransmitHandshake delay caller final.wg) :
    clockGap final caller ∧ retransmitObservation final pid = some (some (caller + delay.toUInt64)) := by
  obtain ⟨now, unit, low, high, effect⟩ := effect
  by_cases same : p.timer .retransmitHandshake = some (caller + delay.toUInt64)
  · simp only [same, ite_true] at effect
    constructor
    · exact ⟨now, by rw [effect]; rfl, low, high⟩
    · simp only [retransmitObservation, Campaign2.Snapshot.peerAt, effect,
        recordedArmPrefixView, device, Option.bind_some, resident, Option.map_some]
      exact congrArg some same
  · simp only [same, ite_false] at effect
    obtain ⟨clk, effect⟩ := effect
    cases placement : TimerWheel.place p .retransmitHandshake (caller + delay.toUInt64) clk <;>
      simp only [wheelPlacementView, placement] at effect
    all_goals
      constructor
      · exact ⟨now, by rw [effect]; rfl, low, high⟩
      · simp [retransmitObservation, Campaign2.Snapshot.peerAt, effect,
          recordedArmPrefixView, device, Peer.setTimer, Peer.setWheel]

theorem initiationRearmExecution_effect (pid : PeerId) (entry : InitiationView) :
    Campaign2.Product.Ensures (initiationRearmExecution pid)
      (fun s => initiationObservation s.toSnapshot pid = some entry)
      (fun arm final => RearmCertificate pid entry arm final) := by
  intro initial arm final pre run
  rw [initiationRearmExecution_run] at run
  cases hs : (liftWG (sendHandshakeInitiation pid)).run initial with
  | error e => rw [hs] at run; cases run
  | ok pair =>
    obtain ⟨u, beforeRelease⟩ := pair
    cases u
    rw [hs] at run
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
    obtain ⟨reached, beforeArm, prefixRun, finish⟩ :=
      source_initiation_arm_path pid initial beforeRelease hs
    have nativePrefix : ((initiationArmPrefix pid).run initial.wg).run initial.ambient =
        .ok ((reached, beforeArm.wg), beforeArm.ambient) := by
      change (((initiationArmPrefix pid).run initial.wg).run initial.ambient >>= _) = _ at prefixRun
      cases actual : ((initiationArmPrefix pid).run initial.wg).run initial.ambient with
      | error stop => rw [actual] at prefixRun; cases prefixRun
      | ok pair =>
        obtain ⟨⟨value, current⟩, inputs⟩ := pair
        rw [actual] at prefixRun
        cases prefixRun
        rfl
    have preserved := (ensures_iff _ _ _).mpr (initiationArmPrefix_view pid entry)
      initial.wg initial.ambient reached beforeArm.wg beforeArm.ambient pre nativePrefix
    refine ⟨reached, Campaign2.Product.snapshot beforeArm,
      Campaign2.Product.observeResult ((clockJitterPath .timerJiffiesHandshakeInitiated .retransmitJitter).run beforeArm),
      ?_, preserved, ?_⟩
    · exact observe_ok (prefixInspect_run _ _ initial beforeArm reached prefixRun)
    · intro d p device resident reaches running alive records
      subst reached
      obtain ⟨caller, afterRead, jitter, afterJitter, read, draw, bounded, effect⟩ :=
        source_initiation_send_arm pid d p resident running alive initial beforeArm beforeRelease
          prefixRun device records hs
      obtain ⟨gap, expiry⟩ := recordedRetransmit_observations pid p
        (Campaign2.Product.snapshot beforeArm).toSnapshot (Campaign2.Product.snapshot beforeRelease).toSnapshot
        d (REKEY_TIMEOUT_TICKS + jitter) caller device resident effect
      exact ⟨caller, Campaign2.Product.snapshot afterRead, jitter, Campaign2.Product.snapshot afterJitter,
        observe_ok (clockJitterPath_run _ _ _ _ _ _ _ read draw), bounded, effect, gap, expiry⟩

theorem rearmWorkerBody_effect (pid : PeerId) (entry : InitiationView)
    (retained : 1 < entry.2.2.1) :
    Campaign2.Product.Ensures (rearmWorkerBody pid)
      (fun s => initiationObservation s.toSnapshot pid = some entry)
      (fun arm final => RearmCertificate pid entry arm final) := by
  intro initial arm final pre run
  simp only [rearmWorkerBody, StateT.run_bind] at run
  cases hi : (initiationRearmExecution pid).run initial with
  | error e => rw [hi] at run; cases run
  | ok pair =>
    obtain ⟨observedArm, beforeRelease⟩ := pair
    rw [hi] at run
    change ((liftWG (peerPut (some pid))).run beforeRelease >>= fun out =>
      Except.ok (observedArm, out.2)) = .ok (arm, final) at run
    cases hp : (liftWG (peerPut (some pid))).run beforeRelease with
    | error e => rw [hp] at run; cases run
    | ok pair =>
      obtain ⟨u, afterRelease⟩ := pair
      rw [hp] at run
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
      have sendRun : (liftWG (sendHandshakeInitiation pid)).run initial = .ok ((), beforeRelease) := by
        rw [← initiationRearmExecution_erase]
        change ((initiationRearmExecution pid).run initial >>= fun out => Except.ok ((), out.2)) = _
        rw [hi]; rfl
      have nativeSend : ((sendHandshakeInitiation pid).run initial.wg).run initial.ambient =
          .ok (((), beforeRelease.wg), beforeRelease.ambient) := by
        change (((sendHandshakeInitiation pid).run initial.wg).run initial.ambient >>= _) = _ at sendRun
        cases actual : ((sendHandshakeInitiation pid).run initial.wg).run initial.ambient with
        | error stop => rw [actual] at sendRun; cases sendRun
        | ok pair =>
          obtain ⟨⟨value, current⟩, inputs⟩ := pair
          rw [actual] at sendRun
          cases sendRun
          rfl
      have held := sendHandshakeInitiation_workerView pid (initiationWorkerView entry)
        initial.wg initial.ambient () beforeRelease.wg beforeRelease.ambient
        (workerAt_of_initiationAt initial.wg pid entry pre) nativeSend
      obtain ⟨reached, beforeArm, tail, path, atArm, conditional⟩ :=
        initiationRearmExecution_effect pid entry initial observedArm beforeRelease pre hi
      refine ⟨reached, beforeArm, tail, path, atArm, ?_⟩
      intro d p device resident reaches running alive records
      obtain ⟨caller, afterRead, jitter, afterJitter, actual, bound, peer, gap, expiry⟩ :=
        conditional d p device resident reaches running alive records
      refine ⟨caller, afterRead, jitter, afterJitter, actual, bound, peer, gap, ?_⟩
      have nativePut : ((peerPut (some pid)).run beforeRelease.wg).run beforeRelease.ambient =
          .ok ((u, afterRelease.wg), afterRelease.ambient) := by
        change (((peerPut (some pid)).run beforeRelease.wg).run beforeRelease.ambient >>= _) = _ at hp
        cases actual : ((peerPut (some pid)).run beforeRelease.wg).run beforeRelease.ambient with
        | error stop => rw [actual] at hp; cases hp
        | ok pair =>
          obtain ⟨⟨value, current⟩, inputs⟩ := pair
          rw [actual] at hp
          cases hp
          rfl
      exact retained_peerPut_workerView_retransmit_variant pid entry.1 entry.2.1 entry.2.2.1
        _ retained beforeRelease.wg beforeRelease.ambient u afterRelease.wg afterRelease.ambient
        ⟨held, expiry⟩ nativePut

theorem sendRearmExecution_effect (d : Device) (units : List (Nat × Nat × Nat))
    (retained : RetainedSendQueue d) :
    Campaign2.Product.Ensures sendRearmExecution
      (fun s => s.wg.device = some d ∧ s.ambient.unitPeers = units)
      (fun execution final => ∃ p, d.peers[execution.send.pid]? = some p ∧
        RearmCertificate execution.send.pid (initiationView p) execution.arm final) := by
  intro w execution final pre run
  change (sendWorkerSelection.run w >>= fun sel =>
    (sendWorkerDequeue sel.1.2).run sel.2 >>= fun deq =>
    (hidden (.sectionStart .sendWorker) : Leanux.M (List UInt8)).run deq.2 >>= fun start =>
    (rearmWorkerBody sel.1.2).run start.2 >>= fun body =>
    (hidden (.sectionStop .sendWorker) : Leanux.M (List UInt8)).run body.2 >>= fun stop =>
    Except.ok (SendRearmExecution.mk (SendWorkerExecution.mk sel.1.1 sel.1.2 (Campaign2.Product.snapshot deq.2)
      start.1 (Campaign2.Product.snapshot start.2) (Campaign2.Product.snapshot body.2) stop.1) body.1, stop.2)) =
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
      cases hb : (hidden (.sectionStart .sendWorker) : Leanux.M (List UInt8)).run beforeSection with
      | error e => simp only [hb] at run; cases run
      | ok pair =>
        obtain ⟨bytes, afterStart⟩ := pair
        simp only [hb] at run
        cases hw : (rearmWorkerBody selected.2).run afterStart with
        | error e => simp only [hw] at run; cases run
        | ok pair =>
          obtain ⟨arm, afterBody⟩ := pair
          simp only [hw] at run
          cases he : (hidden (.sectionStop .sendWorker) : Leanux.M (List UInt8)).run afterBody with
          | error e => simp only [he] at run; cases run
          | ok pair =>
            obtain ⟨stopBytes, afterStop⟩ := pair
            simp only [he] at run
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj run)
            have selection := sendWorkerSelection_effect d units w selected afterSelection pre hs
            obtain ⟨p, resident, pending, deq⟩ :=
              sendWorkerDequeue_effect selected.2 d afterSelection _ beforeSection selection.1 hd
            have startWG : afterStart.wg = beforeSection.wg := by
              change ((AmbientM.hidden (.sectionStart .sendWorker)).run beforeSection.ambient >>= _) = _ at hb
              cases actual : (AmbientM.hidden (.sectionStart .sendWorker)).run beforeSection.ambient with
              | error stop => rw [actual] at hb; cases hb
              | ok pair => rw [actual] at hb; cases hb; rfl
            have start : afterStart.wg.dev = some (dequeuedSendDevice d selected.2 p) := by
              rw [startWG]
              exact deq
            have bodyPre : initiationAt afterStart.wg selected.2 = some (initiationView p) := by
              simp [initiationAt, peerAt, start, dequeuedSendDevice, initiationView]
            have body := rearmWorkerBody_effect selected.2 (initiationView p)
              (retained selected.2 selection.2.2.1 p resident) afterStart arm afterBody bodyPre hw
            obtain ⟨reached, beforeArm, tail, path, atArm, conditional⟩ := body
            refine ⟨p, resident, reached, beforeArm, tail, path, atArm, ?_⟩
            intro armDev armPeer device stored reaches running alive records
            obtain ⟨caller, afterRead, jitter, afterJitter, actual, bound, peer, gap, expiry⟩ :=
              conditional armDev armPeer device stored reaches running alive records
            refine ⟨caller, afterRead, jitter, afterJitter, actual, bound, peer, gap, ?_⟩
            have stopWG : afterStop.wg = afterBody.wg := by
              change ((AmbientM.hidden (.sectionStop .sendWorker)).run afterBody.ambient >>= _) = _ at he
              cases actual : (AmbientM.hidden (.sectionStop .sendWorker)).run afterBody.ambient with
              | error stop => rw [actual] at he; cases he
              | ok pair => rw [actual] at he; cases he; rfl
            change ((afterStop.wg.dev.bind fun d => d.peers[selected.2]?).map Peer.timerRetransmitHandshake) = _
            rw [stopWG]
            exact expiry

end Leanux.Proofs.WG.TimerDiscipline
