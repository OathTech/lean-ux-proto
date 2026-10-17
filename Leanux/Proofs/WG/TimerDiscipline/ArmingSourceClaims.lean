import Leanux.Proofs.WG.TimerDiscipline.ArmingSource
import Leanux.Proofs.WG.TimerDiscipline.RetrySource

/-! Original timer source contracts projected over the current native state.
The exact-peer arming and deletion statements explicitly include the wheel
representation; their original normal-return domains remain unchanged. -/
set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Campaign2

theorem source_recorded_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (p : Peer) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (armTimer pid timer delay (some caller))
      (fun s => s = entry ∧ s.ambient.armRecords = true ∧ s.peerAt pid = some p)
      (fun _ final => ∃ now unit,
        0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1 ∧
        if p.timer timer = some (caller + delay.toUInt64) then
          final.wg = recordedArmPrefixView entry.wg pid timer now unit
        else ∃ clk, final.wg = wheelPlacementView
          {recordedArmPrefixView entry.wg pid timer now unit with timerClk := some clk}
          pid p timer (caller + delay.toUInt64) clk) :=
  armTimer_recorded pid timer delay caller p entry


theorem source_delete (pid : PeerId) (timer : PeerTimer) (p : Peer)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (delTimer pid timer)
      (fun s => s = entry ∧ s.peerAt pid = some p)
      (fun _ final => final = delTimerView entry pid p timer) :=
  delTimer_exact pid timer p entry


/-- The arm guard retains its original result and device preservation. -/
theorem source_arm_guard (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (modPeerTimerGuard pid) (fun s => s.wg.device = some d)
      (fun allowed s => allowed = (d.running && !p.isDead) ∧ s.wg.device = some d) := by
  intro g ambient result final after pre run
  exact modPeerTimerGuard_exact pid d p resident g ambient result final after pre run


theorem source_guarded_arm (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p)
    (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (modPeerTimer site pid timer delay)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun allowed final => allowed = (d.running && !p.isDead) ∧
        if allowed then peerTimerArmEffect entry pid p timer delay final.wg
        else final.wg = entry.wg) :=
  modPeerTimer_effect site pid timer delay d p resident entry


theorem source_traversal (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersTraversal pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false then
        peerTimerArmEffect entry pid p .persistentKeepalive (p.persistentKeepaliveInterval * HZ) final.wg
      else final.wg = entry.wg) :=
  timersTraversal_effect pid d p resident entry


theorem source_session_derived (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersSessionDerived pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if d.running && !p.isDead then
        peerTimerArmEffect entry pid p .zeroKeyMaterial ZERO_KEY_MATERIAL_TICKS final.wg
      else final.wg = entry.wg) :=
  timersSessionDerived_effect pid d p resident entry


theorem source_data_received (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersDataReceived pid)
      (fun s => s = entry ∧ s.wg.device = some d)
      (fun _ final => if d.running then
        if p.timerPending .sendKeepalive then
          final.wg = {entry.wg with device := some {d with peers := d.peers.insert pid {p with timerNeedAnotherKeepalive := true}}}
        else if p.isDead then final.wg = entry.wg
        else peerTimerArmEffect entry pid p .sendKeepalive KEEPALIVE_TIMEOUT_TICKS final.wg
      else final.wg = entry.wg) :=
  timersDataReceived_effect pid d p resident entry


theorem source_handshake_complete (pid : PeerId) (site : HiddenSite) (p : Peer) :
    Campaign2.Ensures (timersHandshakeComplete pid site)
      (fun s => s.peerAt pid = some p)
      (fun _ s => ∃ now, s.peerAt pid = some
        {((p.setTimer .retransmitHandshake none).setWheel .retransmitHandshake none) with
          timerHandshakeAttempts := 0, sentLastminuteHandshake := false,
          walltimeLastHandshake := now}) :=
  timersHandshakeComplete_effect pid site p


/-- Authenticated sending clears the expiry and wheel entry, preserving the
complete snapshot elsewhere. -/
theorem source_authenticated_sent (pid : PeerId) (p : Peer) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersAnyAuthenticatedPacketSent pid)
      (fun s => s = entry ∧ s.peerAt pid = some p)
      (fun _ final => final = delTimerView entry pid p .sendKeepalive) :=
  delTimer_exact pid .sendKeepalive p entry

/-- Authenticated receipt clears the expiry and wheel entry, preserving the
complete snapshot elsewhere. -/
theorem source_authenticated_received (pid : PeerId) (p : Peer) (entry : Campaign2.Snapshot) :
    Campaign2.Ensures (timersAnyAuthenticatedPacketReceived pid)
      (fun s => s = entry ∧ s.peerAt pid = some p)
      (fun _ final => final = delTimerView entry pid p .newHandshake) :=
  delTimer_exact pid .newHandshake p entry

/-- Normal retransmit callbacks retain their original attempt-count, allocation
identity and retransmit-expiry guarantees; this does not assert a whole episode. -/
theorem source_retransmit_counter (pid : PeerId) (p : Peer) :
    Campaign2.Ensures (expiredRetransmitHandshake pid) (fun s => s.peerAt pid = some p)
      (fun _ s => ∃ q, s.peerAt pid = some q ∧ q.internalId = p.internalId ∧
        q.timerHandshakeAttempts =
          (if p.timerHandshakeAttempts > 18 then p.timerHandshakeAttempts else p.timerHandshakeAttempts + 1) ∧
        q.timerRetransmitHandshake = p.timerRetransmitHandshake) := by
  intro g ambient result final after pre run
  change Noise.peerAt g pid = some p at pre
  have effect := expiredRetransmit_retryView pid p.internalId p.timerHandshakeAttempts
    p.timerRetransmitHandshake g ambient result final after
    (by simp [retryAt, retryView, pre]) run
  change ∃ q, Noise.peerAt final pid = some q ∧ q.internalId = p.internalId ∧
    q.timerHandshakeAttempts =
      (if p.timerHandshakeAttempts > 18 then p.timerHandshakeAttempts else p.timerHandshakeAttempts + 1) ∧
    q.timerRetransmitHandshake = p.timerRetransmitHandshake
  cases resident : Noise.peerAt final pid with
  | none => simp [retryAt, resident] at effect
  | some q =>
    refine ⟨q, rfl, ?_⟩
    simpa [retryAt, retryView, resident, nextAttempts, MAX_TIMER_HANDSHAKES, REKEY_TIMEOUT] using effect

end Leanux.Proofs.WG.TimerDiscipline
