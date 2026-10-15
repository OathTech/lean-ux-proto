import Leanux.Proofs.WG.TimerDiscipline.AbsentGiveUpModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Total execution of the original absent-timer give-up branch. Its premises
check input data and entry state, never assume successful execution. -/
theorem absentGiveUp_run (pid : PeerId) (d : Device) (p : Peer)
    (input : GiveUpArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (absent : p.timerZeroKeyMaterial = none)
    (running : d.running = true) (alive : p.isDead = false)
    (valid : input.Valid) (entry : World) (device : entry.k.wg = some d)
    (mode : entry.armRecords = true) (records : entry.hidden = some (input.records rest)) :
    (expiredRetransmitHandshake pid).run entry = .ok ((),
      { entry with
        k := { entry.k with wg := some (absentGiveUpDevice d pid p input) }
        steps := absentGiveUpSteps p entry.netRxSection entry.steps
        hidden := some rest
        jiffiesLast := some input.now
        timerUnits := absentGiveUpUnits pid input entry.timerUnits }) := by
  obtain ⟨callerLength, armLength, expiry, gapLow, gapHigh⟩ := valid
  have callerDrop : input.callerData.drop 8 = [] := by simp [← callerLength]
  have callerTake : input.callerData.take 8 = input.callerData := by simp [← callerLength]
  have armDrop : input.armData.drop 24 = [] := by simp [← armLength]
  have armTake : input.armData.take 24 = input.armData := by simp [← armLength]
  have callerPassive : HiddenSite.passive HiddenSite.timerJiffiesRetransmitZeroKey.info.id = false := by decide
  have armPassive : HiddenSite.passive HiddenSite.modTimerArm.info.id = false := by decide
  have notLow : ¬ (input.now - input.caller).toInt64 < 0 := by
    rw [Int64.lt_iff_toInt_lt]
    have bound := Int64.le_iff_toInt_le.mp gapLow
    omega
  have notHigh : ¬ 1 < (input.now - input.caller).toInt64 := by
    rw [Int64.lt_iff_toInt_lt]
    have bound := Int64.le_iff_toInt_le.mp gapHigh
    omega
  change HiddenSite.passive 420 = false at callerPassive
  change HiddenSite.passive 100 = false at armPassive
  simp only [GiveUpArmInput.caller, GiveUpArmInput.now] at expiry notLow notHigh
  simp [-Int64.not_lt] at notLow notHigh
  by_cases unitZero : recordWord input.armData 2 = 0
  all_goals simp [unitZero, expiredRetransmitHandshake, getPeer, getDev, getK, setPeer, modifyDev,
    modifyK, branchCmp, branch, delTimer, purgeStagedPackets, device, resident,
    limit, absent, Peer.setTimer, Peer.timerPending, Peer.timer,
    modPeerTimer, callerJiffies, hiddenJiffies, hidden, skipAmbient, noteNetRxStart,
    modPeerTimerGuard, Leanux.WG.andM, armTimer, mode, records, GiveUpArmInput.records,
    callerPassive, armPassive, HiddenSite.info, callerLength, armLength,
    callerDrop, callerTake, armDrop, armTake, running, alive,
    GiveUpArmInput.caller, GiveUpArmInput.now, GiveUpArmInput.unit,
    giveUpDevice, giveUpPeer, absentGiveUpDevice, absentGiveUpSteps, absentGiveUpUnits,
    expiry, notLow, notHigh, List.dropWhile_cons,
    Functor.map, Functor.discard, Functor.mapConst, Function.const, StateT.map,
    StateT.run_bind, StateT.run_pure, StateT.run, Bind.bind, Pure.pure, get, getThe,
    MonadStateOf.get, set, modify, modifyGet, StateT.bind, StateT.pure, StateT.get,
    StateT.set, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure, Worker.sectionId, Worker.index]

end Leanux.Proofs.WG.TimerDiscipline
