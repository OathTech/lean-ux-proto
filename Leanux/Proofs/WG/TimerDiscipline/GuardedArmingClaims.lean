import Leanux.Proofs.WG.TimerDiscipline.ArmingClaims
import Leanux.Proofs.WG.TimerDiscipline.TimerInputFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

def peerTimerArmEffect (entry : Campaign2.Snapshot) (pid : PeerId) (p : Peer)
    (timer : PeerTimer) (delay : Nat) (final : Campaign2.State) : Prop :=
  if entry.ambient.armRecords then
    ∃ caller now unit, 0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 ∧
      if p.timer timer = some (caller + delay.toUInt64) then
        final = recordedArmPrefixView entry.wg pid timer now unit
      else ∃ clk, final = wheelPlacementView
        {recordedArmPrefixView entry.wg pid timer now unit with timerClk := some clk}
        pid p timer (caller + delay.toUInt64) clk
  else
    final = wheelPlacementView entry.wg pid p timer
      (entry.wg.jiffiesLast.getD 0 + delay.toUInt64) (entry.wg.jiffiesLast.getD 0)

theorem modPeerTimer_effect (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (modPeerTimer site pid timer delay)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun allowed final => allowed = (d.running && !p.isDead) ∧
        if allowed then peerTimerArmEffect entry pid p timer delay final.wg
        else final.wg = entry.wg) := by
  intro g ambient result final after pre run
  rcases pre with ⟨rfl, device⟩
  change g.dev = some d at device
  change (((callerJiffies site).run g).run ambient >>= fun ((caller, current), inputs) =>
    ((do
      if ← modPeerTimerGuard pid then
        armTimer pid timer delay caller
        return true
      return false : WG.M Bool).run current).run inputs) = _ at run
  cases read : ((callerJiffies site).run g).run ambient with
  | error err => rw [read] at run; cases run
  | ok out =>
    obtain ⟨⟨caller, current⟩, inputs⟩ := out
    obtain ⟨unchanged, readMode, callerMode⟩ := callerJiffies_input_effect site g current ambient inputs caller read
    subst current
    rw [read] at run
    change (((modPeerTimerGuard pid).run g).run inputs >>= fun ((allowed, current), checked) =>
      ((if allowed then do armTimer pid timer delay caller; pure true else pure false : WG.M Bool).run current).run checked) = _ at run
    cases guard : ((modPeerTimerGuard pid).run g).run inputs with
    | error err => rw [guard] at run; cases run
    | ok out =>
      obtain ⟨⟨allowed, current⟩, checked⟩ := out
      obtain ⟨value, unchanged, guardMode⟩ := modPeerTimerGuard_input_effect pid d p resident
        g current inputs checked allowed device guard
      subst current
      have checkedMode : checked.armRecords = ambient.armRecords := guardMode.trans readMode
      rw [guard] at run
      cases allowed with
      | false =>
        cases run
        exact ⟨value, rfl⟩
      | true =>
        change (((armTimer pid timer delay caller).run g).run checked >>= fun ((_, current), next) =>
          .ok ((true, current), next)) = _ at run
        cases armed : ((armTimer pid timer delay caller).run g).run checked with
        | error err => rw [armed] at run; cases run
        | ok out =>
          obtain ⟨⟨u, current⟩, next⟩ := out
          cases u
          rw [armed] at run
          cases run
          refine ⟨value, ?_⟩
          have hp : peerAt g pid = some p := by simp [peerAt, device, resident]
          cases mode : ambient.armRecords with
          | false =>
            have off : checked.armRecords = false := checkedMode.trans mode
            have effect := armTimer_off_effect pid timer delay caller g p hp checked after final off armed
            change peerTimerArmEffect (Campaign2.snapshot g ambient) pid p timer delay
              (Campaign2.snapshot final after).wg
            simp only [peerTimerArmEffect, Campaign2.snapshot, mode, Bool.false_eq_true, ite_false]
            rw [effect]
            cases placement : TimerWheel.place p timer (g.jiffiesLast.getD 0 + delay.toUInt64) (g.jiffiesLast.getD 0) <;>
              simp only [wheelPlacementState, wheelPlacementView, placement]
            all_goals rfl
          | true =>
            have on : checked.armRecords = true := checkedMode.trans mode
            cases caller with
            | none => simp [mode] at callerMode
            | some caller =>
              have effect := armTimer_recorded pid timer delay caller p
                (Campaign2.snapshot g checked) g checked () final after ⟨rfl, on, hp⟩ armed
              obtain ⟨now, unit, low, high, exactState⟩ := effect
              change peerTimerArmEffect (Campaign2.snapshot g ambient) pid p timer delay
                (Campaign2.snapshot final after).wg
              simp only [peerTimerArmEffect, Campaign2.snapshot, mode, ite_true]
              exact ⟨caller, now, unit, low, high, exactState⟩


theorem timersSessionDerived_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersSessionDerived pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if d.running && !p.isDead then
        peerTimerArmEffect entry pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS final.wg
      else final.wg = entry.wg) := by
  intro g ambient result final after pre run
  change (((modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).run g).run ambient >>=
    fun ((_, current), inputs) => .ok (((), current), inputs)) = _ at run
  cases arm : ((modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).run g).run ambient with
  | error err => rw [arm] at run; cases run
  | ok out =>
    obtain ⟨⟨allowed, current⟩, inputs⟩ := out
    rw [arm] at run
    cases run
    obtain ⟨value, effect⟩ := modPeerTimer_effect .timerJiffiesSessionDerived pid
      .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS d p resident entry
      g ambient allowed final after pre arm
    simpa only [value] using effect

end Leanux.Proofs.WG.TimerDiscipline
