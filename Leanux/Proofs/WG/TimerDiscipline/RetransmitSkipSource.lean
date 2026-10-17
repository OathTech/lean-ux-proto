import Leanux.Proofs.WG.TimerDiscipline.RetransmitReadyModel
import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterSource
import Leanux.Proofs.WG.TimerDiscipline.JitterRecordsSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2
theorem retransmitCaller_run (input : RetransmitArmInput) (rest : List HiddenRecord)
    (len : input.callerData.length = 8) (w : World) (mode : w.ambient.armRecords = true)
    (records : w.ambient.hidden = some ({ site := HiddenSite.timerJiffiesHandshakeInitiated.info.id, bytes := input.callerData } :: rest)) :
    (liftWG (callerJiffies .timerJiffiesHandshakeInitiated)).run w =
      .ok (some input.caller, {w with ambient := {w.ambient with hidden := some rest}}) := by
  have passive : HiddenSite.passive HiddenSite.timerJiffiesHandshakeInitiated.info.id = false := by decide
  have drop : input.callerData.drop 8 = [] := by simp [← len]
  have take : input.callerData.take 8 = input.callerData := by simp [← len]
  change HiddenSite.passive 424 = false at passive
  have ambientLift {α : Type} (action : AmbientM α) :
      (monadLift action : WG.M α) = StateT.lift action := rfl
  have native : ((callerJiffies .timerJiffiesHandshakeInitiated).run w.wg).run w.ambient =
      .ok ((some input.caller, w.wg), {w.ambient with hidden := some rest}) := by
    change ((if w.ambient.armRecords then
      (some <$> hiddenJiffies .timerJiffiesHandshakeInitiated : WG.M (Option UInt64))
      else pure none).run w.wg).run w.ambient = _
    rw [mode]
    simp only [ite_true, hiddenJiffies, AmbientM.hiddenJiffies, ambientLift,
      map_eq_pure_bind, StateT.run_bind, StateT.run_lift, StateT.run_pure,
      bind_assoc, pure_bind]
    simp [AmbientM.hidden, AmbientM.skipAmbient, AmbientM.noteNetRxStart,
      records, HiddenSite.info, passive, len, drop, take, RetransmitArmInput.caller,
      Worker.sectionId, Worker.index]
    rfl
  change (((callerJiffies .timerJiffiesHandshakeInitiated).run w.wg).run w.ambient >>= _) = _
  rw [native]
  rfl

theorem retransmitGuardSkip_run (pid : PeerId) (d : Device) (p : Peer)
    (delay : Nat) (caller : UInt64) (resident : d.peers[pid]? = some p)
    (inactive : (d.running && !p.isDead) = false) (w : World) (device : w.wg.dev = some d) :
    (liftWG (armIfGuard pid .retransmitHandshake delay caller)).run w =
      .ok ((), {w with ambient := {w.ambient with steps := retransmitSkippedSteps d.running w.ambient.netRxSection w.ambient.steps}}) := by
  have guard : ((modPeerTimerGuard pid).run w.wg).run w.ambient =
      .ok ((false, w.wg), {w.ambient with
        steps := retransmitSkippedSteps d.running w.ambient.netRxSection w.ambient.steps}) := by
    cases running : d.running <;> cases dead : p.isDead <;>
      simp [running, dead] at inactive
    all_goals simp [modPeerTimerGuard, Leanux.WG.andM, branch, AmbientM.branch,
      getPeer, getDev, device, resident, running, dead, retransmitSkippedSteps]
    all_goals rfl
  change ((((modPeerTimerGuard pid).run w.wg).run w.ambient >>= fun ((allowed, current), inputs) =>
    ((if allowed then armTimer pid .retransmitHandshake delay (some caller) else pure () : WG.M Unit).run current).run inputs) >>= _) = _
  rw [guard]
  rfl

theorem retransmitSkipped_run (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (inactive : (d.running && !p.isDead) = false)
    (valid : input.Valid) (w : World) (device : w.wg.dev = some d)
    (mode : w.ambient.armRecords = true) (records : w.ambient.hidden = some (input.records rest)) :
    (liftWG (timersHandshakeInitiated pid)).run w =
      .ok ((), {w with ambient := {w.ambient with
        hidden := some ({site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest)
        steps := retransmitSkippedSteps d.running w.ambient.netRxSection w.ambient.steps}}) := by
  let afterJitter := {site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest
  let draws := jitterStream .retransmit input.rejected input.accepted afterJitter
  have caller := retransmitCaller_run input draws valid.1 w mode records
  -- Local form of campaign 1's Framing.liftWG_bind, also used by ArmingPrefixesSource.
  have liftBind {α β : Type} (action : WG.M α) (next : α → WG.M β) :
      liftWG (action >>= next) = (liftWG action >>= fun x => liftWG (next x)) := by
    have lifted {γ : Type} (a : WG.M γ) (entry) :
        (liftWG a).run entry = ((a.run entry.wg).run entry.ambient).map
          (fun ((x, g), ambient) => (x, {entry with wg := g, ambient})) := by
      unfold liftWG StateT.run
      cases a entry.wg entry.ambient <;> rfl
    funext entry
    change (liftWG (action >>= next)).run entry =
      (liftWG action >>= fun x => liftWG (next x)).run entry
    rw [lifted]
    simp only [StateT.run_bind]
    rw [lifted]
    cases actual : (action.run entry.wg).run entry.ambient with
    | error stop => rfl
    | ok out =>
      obtain ⟨⟨value, current⟩, ambient⟩ := out
      simp only [Except.map]
      exact (lifted (next value) {entry with wg := current, ambient}).symm
  have source : liftWG (timersHandshakeInitiated pid) = (do
      let caller ← liftWG (callerJiffies .timerJiffiesHandshakeInitiated)
      let jitter ← liftWG (jitterBelowRekeyTimeout JitterSite.retransmit.hiddenSite)
      liftWG (do if ← modPeerTimerGuard pid then
        armTimer pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + jitter) caller)) := by
    rw [handshakeInitiated_source, jitteredArm, liftBind]
    congr 1
    funext value
    exact liftBind _ _
  rw [source, StateT.run_bind, caller]
  change ((liftWG (jitterBelowRekeyTimeout JitterSite.retransmit.hiddenSite)).run
      {w with ambient := {w.ambient with hidden := some draws}} >>= fun out =>
    (liftWG (armIfGuard pid .retransmitHandshake (REKEY_TIMEOUT_TICKS + out.1) input.caller)).run out.2) = _
  have jitter : (liftWG (jitterBelowRekeyTimeout JitterSite.retransmit.hiddenSite)).run
      {w with ambient := {w.ambient with hidden := some draws}} =
      .ok (jitterValue input.accepted, {w with ambient := {w.ambient with hidden := some afterJitter}}) := by
    change (((jitterBelowRekeyTimeout JitterSite.retransmit.hiddenSite).run w.wg).run
      {w.ambient with hidden := some draws} >>= _) = _
    rw [jitter_records .retransmit input.rejected input.accepted afterJitter valid.2.1 valid.2.2.1 _ _ rfl]
    rfl
  rw [jitter]
  exact retransmitGuardSkip_run pid d p input.delay input.caller resident inactive
    {w with ambient := {w.ambient with hidden := some afterJitter}} device

end Leanux.Proofs.WG.TimerDiscipline
