import Leanux.Proofs.WG.TimerDiscipline.ArmingChangedExpirySource
import Leanux.Proofs.WG.TimerDiscipline.ArmingBaseSource

import Leanux.Proofs.WG.TimerDiscipline.RetryGiveUpSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem modPeerTimer_sendQueue (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (queue : Option (List PeerId)) :
    ⦃fun g => ⌜g.dev.map Device.sendWorkQueue = queue⌝⦄ modPeerTimer site pid timer delay
      ⦃⇓? _ g => ⌜g.dev.map Device.sendWorkQueue = queue⌝⦄ := by
  let P : WGWorld → Prop := fun g => g.dev.map Device.sendWorkQueue = queue
  let R : WGWorld → Prop := fun g => P g ∧ ∃ p, peerAt g pid = some p
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hamb {α : Type} (a : AmbientM α) :
      Ensures (StateT.lift a : WG.M α) P (fun _ => P) :=
    (ensures_iff _ _ _).mpr (hoare_liftAmbient_variant a P)
  have wheelFrame (g : WGWorld) (p : Peer) (expires clk : UInt64) :
      (wheelPlacementState g pid p timer expires clk).dev.map Device.sendWorkQueue =
        g.dev.map Device.sendWorkQueue := by
    cases placement : TimerWheel.place p timer expires clk <;>
      cases device : g.dev <;> simp [wheelPlacementState, placement, device]
  have harm (caller : Option UInt64) :
      Ensures (armTimer pid timer delay caller) R (fun _ => P) := by
    intro g ambient result final after pre run
    obtain ⟨preserved, p, resident⟩ := pre
    cases result
    cases mode : ambient.armRecords with
    | false =>
      have effect := armTimer_off_effect pid timer delay caller g p resident
        ambient after final mode run
      rw [effect]
      exact (wheelFrame g p _ _).trans preserved
    | true =>
      cases caller with
      | none =>
        have ambientRead : ((getAmbient : WG.M Ambient).run g).run ambient =
            .ok ((ambient, g), ambient) := rfl
        have hiddenRead : ((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient =
            ((AmbientM.hidden .modTimerArm).run ambient >>= fun (bytes, next) =>
              Except.ok ((bytes, g), next)) := rfl
        simp only [armTimer, StateT.run_bind, StateT.run_get, pure_bind] at run
        rw [ambientRead] at run
        simp only [bind, Except.bind, mode, Bool.not_true, Bool.false_eq_true, ite_false] at run
        change (((hidden .modTimerArm : WG.M (List UInt8)).run g).run ambient >>= _) = _ at run
        rw [hiddenRead] at run
        cases read : (AmbientM.hidden .modTimerArm).run ambient with
        | error err => rw [read] at run; cases run
        | ok out => rw [read] at run; cases out; cases run
      | some caller =>
        by_cases same : p.timer timer = some (caller + delay.toUInt64)
        · obtain ⟨now, unit, _, _, effect⟩ :=
            armTimer_sameExpiry_effect pid timer delay caller g p resident same
              ambient after final mode run
          rw [effect]
          exact preserved
        · obtain ⟨now, unit, clk, _, _, effect⟩ :=
            armTimer_changedExpiry_effect pid timer delay caller g p resident same
              ambient after final mode run
          rw [effect]
          exact (wheelFrame _ p _ _).trans preserved
  have hguard : Ensures (modPeerTimerGuard pid) P (fun _ => R) := by
    intro g ambient result final after pre run
    cases device : g.dev with
    | none =>
      simp [modPeerTimerGuard, getDev, device, invariant, AmbientM.invariant] at run
      cases run
    | some d =>
      cases found : d.peers[pid]? with
      | none =>
        simp [modPeerTimerGuard, getPeer, getDev, device, found, invariant, AmbientM.invariant] at run
        cases run
      | some p =>
        have effect := (modPeerTimerGuard_exact pid d p found
          g ambient result final after device run).2
        constructor
        · simpa only [P, effect, device] using pre
        · exact ⟨p, by simp [peerAt, effect, found]⟩
  have hcaller : Ensures (callerJiffies site) P (fun _ => P) := by
    unfold callerJiffies
    refine ensures_bind _ _ (hamb (get : AmbientM Ambient)) ?_
    intro inputs
    split
    · have mapped := map_result_native_spec some (hiddenJiffies site : WG.M UInt64)
          P (fun _ => P) ((ensures_iff _ _ _).mp (hamb (AmbientM.hiddenJiffies site)))
      intro g ambient result final after pre run
      obtain ⟨tick, _, preserved⟩ :=
        (ensures_iff _ _ _).mpr mapped g ambient result final after pre run
      exact preserved
    · exact hpure _
  apply (ensures_iff _ _ _).mp
  unfold modPeerTimer
  refine ensures_bind _ _ hcaller ?_
  intro caller
  refine ensures_bind _ _ hguard ?_
  intro allowed
  split
  · refine ensures_bind _ _ (harm caller) ?_
    intro _
    exact hpure _
  · intro g ambient result final after pre run
    cases run
    exact pre.1


/-- Giving up clears staged packets and timers but does not queue send work. -/
theorem retransmitGiveUp_sendQueue (pid : PeerId) (queue : Option (List PeerId)) :
    ⦃fun g => ⌜g.dev.map Device.sendWorkQueue = queue⌝⦄ retransmitGiveUp pid
      ⦃⇓? _ g => ⌜g.dev.map Device.sendWorkQueue = queue⌝⦄ := by
  let P : WGWorld → Prop := fun g => g.dev.map Device.sendWorkQueue = queue
  have hpure {α : Type} (x : α) : Ensures (pure x : WG.M α) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    exact pre
  have hpeer : Ensures (getPeer pid) P (fun _ => P) := by
    intro g ambient result final after pre run
    exact ((ensures_iff _ _ _).mpr (getPeer_spec pid P)
      g ambient result final after pre run).1
  have hmodify (f : Device → Device) (same : ∀ d, (f d).sendWorkQueue = d.sendWorkQueue) :
      Ensures (modifyDev f) P (fun _ => P) := by
    intro g ambient result final after pre run
    cases run
    cases device : g.dev <;> simpa only [P, modifyDev, device, Option.map, same] using pre
  have hset (p : Peer) : Ensures (setPeer pid p) P (fun _ => P) :=
    hmodify _ (by intro d; rfl)
  have hdel : Ensures (delTimer pid .sendKeepalive) P (fun _ => P) := by
    unfold delTimer
    exact ensures_bind _ _ hpeer (fun p => hset _)
  have hpurge : Ensures (purgeStagedPackets pid) P (fun _ => P) := by
    unfold purgeStagedPackets
    refine ensures_bind _ _ hpeer ?_
    intro p
    refine ensures_bind _ _ (hmodify _ (by intro d; rfl)) ?_
    intro _
    exact hset _
  have hmod : Ensures (discard <| modPeerTimer .timerJiffiesRetransmitZeroKey pid
      .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS) P (fun _ => P) := by
    have mapped := map_result_native_spec (fun _ : Bool => PUnit.unit)
      (modPeerTimer .timerJiffiesRetransmitZeroKey pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS)
      P (fun _ => P) (modPeerTimer_sendQueue .timerJiffiesRetransmitZeroKey pid
        .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS queue)
    intro g ambient result final after pre run
    obtain ⟨_, _, preserved⟩ := (ensures_iff _ _ _).mpr mapped
      g ambient result final after pre run
    exact preserved
  apply (ensures_iff _ _ _).mp
  unfold retransmitGiveUp
  refine ensures_bind _ _ hdel ?_
  intro _
  refine ensures_bind _ _ hpurge ?_
  intro _
  refine ensures_bind _ _ hpeer ?_
  intro p
  refine ensures_bind _ _
    ((ensures_iff _ _ _).mpr (hoare_liftAmbient_variant
      (AmbientM.branch .retransmitZeroKeyNotPending !(p.timerPending .zeroKeyMaterial)) P)) ?_
  intro absent
  cases absent with
  | false => exact hpure ()
  | true => exact hmod

end Leanux.Proofs.WG.TimerDiscipline
