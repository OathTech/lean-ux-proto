import Leanux.Proofs.WG.TimerDiscipline.RecordedFrames
import Leanux.Proofs.WG.TimerDiscipline.ArmingSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

def afterCaller (pid : PeerId) (timer : PeerTimer) (delay : Nat) (caller : UInt64) : M Bool := do
  if ← modPeerTimerGuard pid then
    armTimer pid timer delay (some caller)
    return true
  return false

theorem afterCaller_recorded (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Ensures (afterCaller pid timer delay caller)
      (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun result w => result = (d.running && !p.isDead) ∧
        if result then
          peerAt w pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
          ∃ now, w.jiffiesLast = some now ∧
            0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1
        else peerAt w pid = some p) := by
  have ha := (ensures_iff _ _ _).mp (armTimer_recorded pid timer delay caller p)
  rw [ensures_iff]
  mvcgen [afterCaller, modPeerTimerGuard, Leanux.WG.andM,
    getPeer, getDev, getK, branch, invariant, ha]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [peerAt]
  all_goals grind only

/-- The original caller-read operation witnesses the expiry equation in
arm-record mode. Supplied records and permitted placeholders are both covered. -/
theorem modPeerTimer_recorded_clock (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (initial final : World) (result : Bool) (device : initial.k.wg = some d)
    (records : initial.armRecords = true)
    (run : (modPeerTimer site pid timer delay).run initial = .ok (result, final)) :
    ∃ caller afterRead,
      (callerJiffies site).run initial = .ok (some caller, afterRead) ∧
      result = (d.running && !p.isDead) ∧
      if result then
        peerAt final pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
        ∃ now, final.jiffiesLast = some now ∧
          0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1
      else peerAt final pid = some p := by
  simp only [modPeerTimer, StateT.run_bind] at run
  cases hr : (callerJiffies site).run initial with
  | error err => rw [hr] at run; cases run
  | ok pair =>
    obtain ⟨value, afterRead⟩ := pair
    have info := (ensures_iff _ _ _).mpr (callerJiffies_recorded_spec site d)
      initial value afterRead ⟨device, records⟩ hr
    cases value with
    | none => simp at info
    | some caller =>
      rw [hr] at run
      have effect := afterCaller_recorded pid timer delay caller d p resident
        afterRead result final info.2 run
      exact ⟨caller, afterRead, rfl, effect⟩

theorem sessionDerived_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (timersSessionDerived pid).run initial = .ok ((), final)) :
    ∃ caller afterRead,
      (callerJiffies .timerJiffiesSessionDerived).run initial = .ok (some caller, afterRead) ∧
      peerAt final pid = some (p.setTimer .zeroKeyMaterial
        (some (caller + ZERO_KEY_MATERIAL_TICKS.toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  change ((modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).run initial
    >>= fun out => pure ((), out.2)) = .ok ((), final) at run
  cases hr : (modPeerTimer .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS).run initial with
  | error err => rw [hr] at run; cases run
  | ok pair =>
    obtain ⟨armed, afterArm⟩ := pair
    rw [hr] at run
    change Except.ok ((), afterArm) = Except.ok ((), final) at run
    have same : afterArm = final := by simpa only [Except.ok.injEq, Prod.mk.injEq, true_and] using run
    subst afterArm
    obtain ⟨caller, afterRead, read, guard, effect⟩ := modPeerTimer_recorded_clock
      .timerJiffiesSessionDerived pid .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS
      d p resident initial final armed device records hr
    have yes : armed = true := by simpa [running, alive] using guard
    subst armed
    exact ⟨caller, afterRead, read, by simpa [running, alive] using effect⟩

end Leanux.Proofs.WG.TimerDiscipline
