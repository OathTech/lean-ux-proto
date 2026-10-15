import Leanux.Proofs.WG.TimerDiscipline.RecordedJitterSource
import Leanux.Proofs.WG.Config.Returns

set_option autoImplicit false
set_option pp.structureInstances false

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

def dataSentPrefix (pid : PeerId) : M Bool := do
  branch .timersDataSentNotPending !((← getPeer pid).timerPending .newHandshake)

theorem dataSent_source (pid : PeerId) :
    timersDataSent pid = (do
      if ← dataSentPrefix pid then
        jitteredArm .timerJiffiesDataSent .newHandshakeJitter pid .newHandshake
          (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS)) := by
  simp only [timersDataSent, dataSentPrefix, jitteredArm, bind_assoc]

theorem dataSentPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false) :
    Returns (dataSentPrefix pid) (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun result w => result = true ∧ w.k.wg = some d ∧ w.armRecords = true) := by
  rw [returns_iff]
  mvcgen [dataSentPrefix, getPeer, getDev, getK, invariant, branch]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem dataSent_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (absent : p.timerPending .newHandshake = false)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (timersDataSent pid).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead jitter afterJitter,
      (dataSentPrefix pid).run initial = .ok (true, beforeRead) ∧
      (callerJiffies .timerJiffiesDataSent).run beforeRead = .ok (some caller, afterRead) ∧
      (jitterBelowRekeyTimeout .newHandshakeJitter).run afterRead = .ok (jitter, afterJitter) ∧
      jitter < HZ / 3 ∧
      peerAt final pid = some (p.setTimer .newHandshake
        (some (caller + (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS + jitter).toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  obtain ⟨ready, beforeRead, hprefix, readyValue, hd, hm⟩ :=
    dataSentPrefix_returns pid d p resident absent initial ⟨device, records⟩
  subst ready
  rw [dataSent_source, StateT.run_bind, hprefix] at run
  change (jitteredArm .timerJiffiesDataSent .newHandshakeJitter pid .newHandshake
    (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS)).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, jitter, afterJitter, hread, hjitter, bound, effect⟩ :=
    jitteredArm_recorded_clock .timerJiffiesDataSent .newHandshakeJitter pid .newHandshake
      (KEEPALIVE_TIMEOUT_TICKS + REKEY_TIMEOUT_TICKS) d p resident running alive
      beforeRead final hd hm run
  exact ⟨beforeRead, caller, afterRead, jitter, afterJitter, hprefix, hread, hjitter, bound, effect⟩

theorem discardedArm_recorded_clock (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (discard (modPeerTimer site pid timer delay) : M Unit).run initial = .ok ((), final)) :
    ∃ caller afterRead,
      (callerJiffies site).run initial = .ok (some caller, afterRead) ∧
      peerAt final pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  change ((modPeerTimer site pid timer delay).run initial >>= fun out => pure ((), out.2)) =
    .ok ((), final) at run
  cases hr : (modPeerTimer site pid timer delay).run initial with
  | error err => rw [hr] at run; cases run
  | ok pair =>
    obtain ⟨armed, afterArm⟩ := pair
    rw [hr] at run
    change Except.ok ((), afterArm) = Except.ok ((), final) at run
    have same : afterArm = final := by simpa only [Except.ok.injEq, Prod.mk.injEq, true_and] using run
    subst afterArm
    obtain ⟨caller, afterRead, read, guard, effect⟩ := modPeerTimer_recorded_clock
      site pid timer delay d p resident initial final armed device records hr
    have yes : armed = true := by simpa [running, alive] using guard
    exact ⟨caller, afterRead, read, by simpa [yes] using effect⟩

def traversalPrefix (pid : PeerId) : M (Nat × Bool) := do
  let interval := (← getPeer pid).persistentKeepaliveInterval
  let enabled ← branchCmp .traversalKeepalive (interval != 0) interval 0
  return (interval, enabled)

theorem traversal_source (pid : PeerId) :
    timersTraversal pid = (do
      let (interval, enabled) ← traversalPrefix pid
      if enabled then
        discard <| modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive (interval * HZ)) := by
  simp only [timersTraversal, traversalPrefix, bind_assoc, pure_bind]

theorem traversalPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0) :
    Returns (traversalPrefix pid) (fun w => w.k.wg = some d ∧ w.armRecords = true)
      (fun result w => result = (p.persistentKeepaliveInterval, true) ∧
        w.k.wg = some d ∧ w.armRecords = true) := by
  rw [returns_iff]
  mvcgen [traversalPrefix, getPeer, getDev, getK, invariant, branchCmp]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

theorem traversal_recorded_clock (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (enabled : p.persistentKeepaliveInterval ≠ 0)
    (running : d.running = true) (alive : p.isDead = false)
    (initial final : World) (device : initial.k.wg = some d) (records : initial.armRecords = true)
    (run : (timersTraversal pid).run initial = .ok ((), final)) :
    ∃ beforeRead caller afterRead,
      (traversalPrefix pid).run initial = .ok ((p.persistentKeepaliveInterval, true), beforeRead) ∧
      (callerJiffies .timerJiffiesTraversal).run beforeRead = .ok (some caller, afterRead) ∧
      peerAt final pid = some (p.setTimer .persistentKeepalive
        (some (caller + (p.persistentKeepaliveInterval * HZ).toUInt64))) ∧
      ∃ now, final.jiffiesLast = some now ∧
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 := by
  obtain ⟨ready, beforeRead, hprefix, readyValue, hd, hm⟩ :=
    traversalPrefix_returns pid d p resident enabled initial ⟨device, records⟩
  subst ready
  rw [traversal_source, StateT.run_bind, hprefix] at run
  change (discard (modPeerTimer .timerJiffiesTraversal pid .persistentKeepalive
    (p.persistentKeepaliveInterval * HZ)) : M Unit).run beforeRead = .ok ((), final) at run
  obtain ⟨caller, afterRead, hread, effect⟩ := discardedArm_recorded_clock
    .timerJiffiesTraversal pid .persistentKeepalive (p.persistentKeepaliveInterval * HZ)
    d p resident running alive beforeRead final hd hm run
  exact ⟨beforeRead, caller, afterRead, hprefix, hread, effect⟩

end Leanux.Proofs.WG.TimerDiscipline
