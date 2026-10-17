import Leanux.Proofs.WG.TimerDiscipline.GuardedArmingClaims
import Leanux.Proofs.WG.TimerDiscipline.ArmingWheelSource

set_option autoImplicit false
open Leanux Leanux.WG

namespace Leanux.Proofs.WG.TimerDiscipline

theorem timersTraversal_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersTraversal pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false then
        peerTimerArmEffect entry pid p .persistentKeepalive (p.persistentKeepaliveInterval * HZ) final.wg
      else final.wg = entry.wg) := by
  intro g ambient result final after pre run
  rcases pre with ⟨rfl, device⟩
  change g.dev = some d at device
  let marked := {ambient with steps := ambient.steps.push {
    decision := Decision.traversalKeepalive, outcome := p.persistentKeepaliveInterval != 0,
    operands := some (p.persistentKeepaliveInterval, 0), netRx := ambient.netRxSection}}
  have source : ((timersTraversal pid).run g).run ambient =
      ((if p.persistentKeepaliveInterval != 0 then
        discard <| modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive (p.persistentKeepaliveInterval * HZ)
      else pure () : WG.M Unit).run g).run marked := by
    simp [timersTraversal, getPeer, getDev, device, resident, branchCmp, AmbientM.branchCmp, marked]
  rw [source] at run
  by_cases interval : p.persistentKeepaliveInterval = 0
  · have disabled : (p.persistentKeepaliveInterval != 0) = false := by simp [interval]
    rw [ite_eq_right (by rw [disabled]; decide)] at run
    change Except.ok (((), g), marked) = .ok ((result, final), after) at run
    have sameG : g = final := congrArg (fun out => out.1.2) (Except.ok.inj run)
    rw [← sameG]
    simp [interval, Campaign2.snapshot]
  · have enabled : (p.persistentKeepaliveInterval != 0) = true := by simpa using interval
    rw [ite_eq_left enabled] at run
    change (((modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive (p.persistentKeepaliveInterval * HZ)).run g).run marked >>=
      fun ((_, current), inputs) => .ok (((), current), inputs)) = _ at run
    cases arm : ((modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive (p.persistentKeepaliveInterval * HZ)).run g).run marked with
    | error err => rw [arm] at run; cases run
    | ok out =>
      obtain ⟨⟨allowed, current⟩, inputs⟩ := out
      rw [arm] at run
      cases run
      obtain ⟨value, effect⟩ := modPeerTimer_effect .timerJiffiesTraversal pid
        .persistentKeepalive (p.persistentKeepaliveInterval * HZ) d p resident
        (Campaign2.snapshot g marked) g marked allowed final after ⟨rfl, device⟩ arm
      rw [value] at effect
      change (if d.running && !p.isDead then
        peerTimerArmEffect (Campaign2.snapshot g ambient) pid p .persistentKeepalive
          (p.persistentKeepaliveInterval * HZ) (Campaign2.snapshot final after).wg
        else (Campaign2.snapshot final after).wg = (Campaign2.snapshot g ambient).wg) at effect
      cases running : d.running <;> cases dead : p.isDead <;>
        simpa [interval, running, dead] using effect

theorem timersDataReceived_effect (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersDataReceived pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if d.running then
        if p.timerPending .sendKeepalive then
          final.wg = {entry.wg with device := some {d with peers := d.peers.insert pid {p with timerNeedAnotherKeepalive := true}}}
        else if p.isDead then final.wg = entry.wg
        else peerTimerArmEffect entry pid p .sendKeepalive KEEPALIVE_TIMEOUT_TICKS final.wg
      else final.wg = entry.wg) := by
  intro g ambient result final after pre run
  rcases pre with ⟨rfl, device⟩
  change g.dev = some d at device
  cases running : d.running with
  | false =>
    simp [timersDataReceived, getDev, device, branch, AmbientM.branch, running] at run
    rcases run with ⟨⟨rfl, rfl⟩, rfl⟩
    rfl
  | true =>
    let first := {ambient with steps := ambient.steps.push {
      decision := Decision.timersDataReceivedRunning, outcome := true, netRx := ambient.netRxSection}}
    let marked := {first with steps := first.steps.push {
      decision := Decision.timersDataReceivedNotPending,
      outcome := !p.timerPending .sendKeepalive, netRx := first.netRxSection}}
    have source : ((timersDataReceived pid).run g).run ambient =
        ((if !p.timerPending .sendKeepalive then
          discard <| modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS
        else
          setPeer pid {p with timerNeedAnotherKeepalive := true} : WG.M Unit).run g).run marked := by
      cases pending : p.timerPending .sendKeepalive <;>
        simp [timersDataReceived, getDev, getPeer, device, resident, branch, AmbientM.branch,
          running, pending, first, marked]
      all_goals rfl
    rw [source] at run
    cases pending : p.timerPending .sendKeepalive with
    | true =>
      simp [pending, setPeer, modifyDev] at run
      have stateEq := congrArg (fun out => out.1.2) (Except.ok.inj run)
      dsimp only at stateEq
      rw [← stateEq]
      simp [Campaign2.snapshot, Campaign2.core, device, running]
    | false =>
      simp only [pending, Bool.not_false, ite_true] at run
      change (((modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).run g).run marked >>=
        fun ((_, current), inputs) => .ok (((), current), inputs)) = _ at run
      cases arm : ((modPeerTimer .timerJiffiesDataReceived pid .sendKeepalive KEEPALIVE_TIMEOUT_TICKS).run g).run marked with
      | error err => rw [arm] at run; cases run
      | ok out =>
        obtain ⟨⟨allowed, current⟩, inputs⟩ := out
        rw [arm] at run
        cases run
        obtain ⟨value, effect⟩ := modPeerTimer_effect .timerJiffiesDataReceived pid
          .sendKeepalive KEEPALIVE_TIMEOUT_TICKS d p resident
          (Campaign2.snapshot g marked) g marked allowed final after ⟨rfl, device⟩ arm
        rw [value] at effect
        change (if d.running && !p.isDead then
          peerTimerArmEffect (Campaign2.snapshot g ambient) pid p .sendKeepalive
            KEEPALIVE_TIMEOUT_TICKS (Campaign2.snapshot final after).wg
          else (Campaign2.snapshot final after).wg = (Campaign2.snapshot g ambient).wg) at effect
        cases dead : p.isDead <;> simpa [running, pending, dead] using effect

theorem timersHandshakeComplete_effect (pid : PeerId) (site : HiddenSite) (p : Peer) :
    Campaign2.Ensures (timersHandshakeComplete pid site)
      (fun s => s.peerAt pid = some p)
      (fun _ s => ∃ now, s.peerAt pid = some
        {((p.setTimer .retransmitHandshake none).setWheel .retransmitHandshake none) with
          timerHandshakeAttempts := 0, sentLastminuteHandshake := false,
          walltimeLastHandshake := now}) := by
  intro g ambient result final after pre run
  exact timersHandshakeComplete_wheel_effect pid site p
    g ambient result final after pre run

end Leanux.Proofs.WG.TimerDiscipline
