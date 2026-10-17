import Leanux.Proofs.WG.TimerDiscipline.RetransmitSkipSource
import Leanux.Proofs.WG.TimerDiscipline.RetransmitReadyModel
import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterSource
import Leanux.Proofs.WG.TimerDiscipline.JitterRecordsSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Total execution of the original retransmit arming hook. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2
theorem retransmitGuardArm_run (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (valid : input.Valid) (w : World) (device : w.k.wg = some d)
    (mode : w.armRecords = true)
    (records : w.hidden = some ({ site := HiddenSite.modTimerArm.info.id, bytes := input.armData } :: rest)) :
    (armIfGuard pid .retransmitHandshake input.delay input.caller).run w =
      .ok ((), {w with
        k := {w.k with wg := some {d with peers := d.peers.insert pid (p.setTimer .retransmitHandshake (some (input.caller + input.delay.toUInt64)))}}
        hidden := some rest
        steps := retransmitReadySteps w.netRxSection w.steps
        jiffiesLast := some input.now
        timerUnits := retransmitReadyUnits pid input w.timerUnits}) := by
  obtain ⟨_, _, _, len, expiry, gapLow, gapHigh⟩ := valid
  have passive : HiddenSite.passive 100 = false := by decide
  have drop : input.armData.drop 24 = [] := by simp [← len]
  have take : input.armData.take 24 = input.armData := by simp [← len]
  have notLow : ¬ (input.now - input.caller).toInt64 < 0 := by
    rw [Int64.lt_iff_toInt_lt]
    have bound := Int64.le_iff_toInt_le.mp gapLow
    omega
  have notHigh : ¬ 1 < (input.now - input.caller).toInt64 := by
    rw [Int64.lt_iff_toInt_lt]
    have bound := Int64.le_iff_toInt_le.mp gapHigh
    omega
  simp only [RetransmitArmInput.now] at notLow notHigh
  simp [-Int64.not_lt] at notLow notHigh
  by_cases unitZero : recordWord input.armData 2 = 0
  all_goals simp [unitZero, armIfGuard, modPeerTimerGuard, Leanux.WG.andM,
    branch, getPeer, getDev, getK, setPeer, modifyDev, modifyK, device, resident,
    running, alive, armTimer, mode, records, hidden, skipAmbient, noteNetRxStart,
    HiddenSite.info, passive, len, drop, take, expiry, notLow, notHigh,
    RetransmitArmInput.now, RetransmitArmInput.unit, retransmitReadySteps, retransmitReadyUnits,
    StateT.run, Bind.bind, Pure.pure, get, getThe,
    MonadStateOf.get, set, modify, modifyGet, StateT.bind, StateT.pure, StateT.get,
    StateT.set, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure, Worker.sectionId, Worker.index]

theorem retransmitReady_run (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (valid : input.Valid) (w : World) (device : w.k.wg = some d)
    (mode : w.armRecords = true) (records : w.hidden = some (input.records rest)) :
    (timersHandshakeInitiated pid).run w =
      .ok ((), {w with
        k := {w.k with wg := some {d with peers := d.peers.insert pid (p.setTimer .retransmitHandshake (some (input.caller + input.delay.toUInt64)))}}
        hidden := some rest
        steps := retransmitReadySteps w.netRxSection w.steps
        jiffiesLast := some input.now
        timerUnits := retransmitReadyUnits pid input w.timerUnits}) := by
  let afterJitter := {site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest
  let draws := jitterStream .retransmit input.rejected input.accepted afterJitter
  have caller := retransmitCaller_run input draws valid.1 w mode records
  rw [handshakeInitiated_source, jitteredArm, StateT.run_bind, caller]
  change ((jitterBelowRekeyTimeout JitterSite.retransmit.hiddenSite).run {w with hidden := some draws}
    >>= fun out => (armIfGuard pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + out.1) input.caller).run out.2) = _
  rw [jitter_records .retransmit input.rejected input.accepted afterJitter valid.2.1 valid.2.2.1 _ rfl]
  exact retransmitGuardArm_run pid d p input rest resident running alive valid
    {w with hidden := some afterJitter} device mode rfl


end Leanux.Proofs.WG.TimerDiscipline
