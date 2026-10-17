import Leanux.Proofs.WG.TimerDiscipline.RetransmitSkipSource

/-! The old active totality conclusions omitted the current wheel records.
These corrected contracts retain every original premise and factor the actual
full Product execution into the actual arm at its proved entry state. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

/-- Exact guard prefix, including the actual arm's success or failure.
The original record predicates remain as intentionally unused domain parameters:
the guard prefix itself consumes no record and asserts no clock/enqueue readiness. -/
theorem retransmitGuardArm_run (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (_valid : input.Valid) (w : World) (device : w.wg.dev = some d)
    (_mode : w.ambient.armRecords = true)
    (_records : w.ambient.hidden = some ({site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest)) :
    (liftWG (armIfGuard pid .retransmitHandshake input.delay input.caller)).run w =
      (liftWG (armTimer pid .retransmitHandshake input.delay (some input.caller))).run
        {w with ambient := {w.ambient with
          steps := retransmitReadySteps w.ambient.netRxSection w.ambient.steps}} := by
  have guard : ((modPeerTimerGuard pid).run w.wg).run w.ambient =
      .ok ((true, w.wg), {w.ambient with
        steps := retransmitReadySteps w.ambient.netRxSection w.ambient.steps}) := by
    simp [modPeerTimerGuard, WG.andM, branch, AmbientM.branch,
      getPeer, getDev, device, resident, running, alive, retransmitReadySteps]
    rfl
  change ((((modPeerTimerGuard pid).run w.wg).run w.ambient >>= fun ((allowed, current), inputs) =>
    ((if allowed then armTimer pid .retransmitHandshake input.delay (some input.caller) else pure () : WG.M Unit).run current).run inputs) >>= _) = _
  rw [guard]
  rfl

/-- The caller and accepted rejection-sampling prefix execute exactly. The
unchanged original active domain then reaches the real arm with all remaining
wheel records and errors retained, rather than guaranteeing a return. -/
theorem retransmitReady_run (pid : PeerId) (d : Device) (p : Peer)
    (input : RetransmitArmInput) (rest : List HiddenRecord)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (valid : input.Valid) (w : World) (device : w.wg.dev = some d)
    (mode : w.ambient.armRecords = true) (records : w.ambient.hidden = some (input.records rest)) :
    (liftWG (timersHandshakeInitiated pid)).run w =
      (liftWG (armTimer pid .retransmitHandshake input.delay (some input.caller))).run
        {w with ambient := {w.ambient with
          hidden := some ({site := HiddenSite.modTimerArm.info.id, bytes := input.armData} :: rest)
          steps := retransmitReadySteps w.ambient.netRxSection w.ambient.steps}} := by
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
  exact retransmitGuardArm_run pid d p input rest resident running alive valid
    {w with ambient := {w.ambient with hidden := some afterJitter}} device mode rfl

end Leanux.Proofs.WG.TimerDiscipline
