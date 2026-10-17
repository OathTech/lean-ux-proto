import Leanux.Proofs.WG.TimerDiscipline.AbsentGiveUpModel
import Leanux.Proofs.WG.TimerDiscipline.RemainingSitesModel
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Execute the actual arm after the proved give-up/caller/guard prefix.
This transforms the actual Product input, preserving every unrelated component;
it never reconstructs an execution state from a projected observation. -/
def absentGiveUpArmContinuation (pid : PeerId) (d : Device) (p : Peer)
    (input : GiveUpArmInput) (rest : List HiddenRecord) : Leanux.M Unit := do
  modify fun initial => {initial with
    wg := {initial.wg with dev := some (giveUpWheelDevice d pid p)}
    ambient := {initial.ambient with
      hidden := some ({site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest)
      steps := absentGiveUpSteps p initial.ambient.netRxSection initial.ambient.steps}}
  liftWG (armTimer pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS (some input.caller))

/-- Correct the former unconditional-success statement: the original domain
proves this exact arm-tail factor, including every error of the current wheel
protocol. MissingClockFindings checks an admitted input whose timerClk read stops.
The original static premises remain; no successful-arm premise is substituted. -/
theorem absentGiveUp_run (pid : PeerId) (d : Device) (p : Peer)
    (input : GiveUpArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p)
    (limit : MAX_TIMER_HANDSHAKES < p.timerHandshakeAttempts)
    (absent : p.timerZeroKeyMaterial = none)
    (running : d.running = true) (alive : p.isDead = false)
    (valid : input.Valid) (entry : World) (device : entry.wg.dev = some d)
    (mode : entry.ambient.armRecords = true)
    (records : entry.ambient.hidden = some (input.records rest)) :
    (liftWG (expiredRetransmitHandshake pid)).run entry =
      (liftWG (armTimer pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS (some input.caller))).run
        {entry with
          wg := {entry.wg with dev := some (giveUpWheelDevice d pid p)}
          ambient := {entry.ambient with
            hidden := some ({site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest)
            steps := absentGiveUpSteps p entry.ambient.netRxSection entry.ambient.steps}} := by
  have callerLength := valid.1
  have callerDrop : input.callerData.drop 8 = [] := by simp [← callerLength]
  have callerTake : input.callerData.take 8 = input.callerData := by simp [← callerLength]
  have callerPassive : HiddenSite.passive 420 = false := by decide
  have ambientLift {α : Type} (action : AmbientM α) :
      (monadLift action : WG.M α) = StateT.lift action := rfl
  simp [liftWG, expiredRetransmitHandshake, getPeer, getDev, setPeer, modifyDev,
    branchCmp, branch, AmbientM.branchCmp, AmbientM.branch, delTimer, purgeStagedPackets,
    device, resident, limit, absent, Peer.setTimer, Peer.setWheel, Peer.timerPending, Peer.timer,
    modPeerTimer, callerJiffies, hiddenJiffies, AmbientM.hiddenJiffies, AmbientM.hidden,
    AmbientM.skipAmbient, AmbientM.noteNetRxStart, getAmbient, ambientLift, StateT.lift,
    modPeerTimerGuard, WG.andM, mode, records, GiveUpArmInput.records,
    callerPassive, HiddenSite.info, callerLength, callerDrop, callerTake, running, alive,
    GiveUpArmInput.caller, giveUpWheelDevice, giveUpWheelPeer, absentGiveUpSteps,
    Functor.map, Functor.discard, Functor.mapConst, Function.const, StateT.map,
    StateT.run, Bind.bind, Pure.pure, get, getThe,
    MonadStateOf.get, set, modify, modifyGet, StateT.bind, StateT.pure, StateT.get,
    StateT.set, MonadStateOf.modifyGet, StateT.modifyGet, Except.bind, Except.pure,
    Worker.sectionId, Worker.index]
  repeat' split at *
  all_goals simp_all
  all_goals subst_vars
  all_goals exact ⟨rfl, rfl⟩

end Leanux.Proofs.WG.TimerDiscipline
