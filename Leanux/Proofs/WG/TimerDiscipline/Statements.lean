import Leanux.Proofs.WG.TimerDiscipline.Arming
import Leanux.Proofs.WG.TimerDiscipline.Jitter

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- A successful recorded arm stores exactly caller jiffies plus delay, with unsigned wrapping; the signed gap to the arm read is zero or one tick. -/
theorem original_recorded_arm (pid : PeerId) (timer : PeerTimer) (delay : Nat)
    (caller : UInt64) (p : Peer) :
    Ensures (armTimer pid timer delay (some caller))
      (fun w => w.armRecords = true ∧ peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (p.setTimer timer (some (caller + delay.toUInt64))) ∧
        ∃ now, w.jiffiesLast = some now ∧
          0 ≤ (now - caller).toInt64 ∧ (now - caller).toInt64 ≤ 1) :=
  armTimer_recorded pid timer delay caller p

/-- Deleting a timer changes exactly that timer field to absent. -/
theorem original_delete (pid : PeerId) (timer : PeerTimer) (p : Peer) :
    Ensures (delTimer pid timer) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (p.setTimer timer none)) :=
  delTimer_exact pid timer p

/-- The arm guard returns running and not dead and leaves the device unchanged. -/
theorem original_arm_guard (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (modPeerTimerGuard pid) (fun w => w.k.wg = some d)
      (fun ok w => ok = (d.running && !p.isDead) ∧ w.k.wg = some d) :=
  modPeerTimerGuard_exact pid d p resident

/-- A normal guarded arm changes only the selected peer timer when running and alive; otherwise it preserves the peer. -/
theorem original_guarded_arm (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (d : Device) (p : Peer) (resident : d.peers[pid]? = some p) :
    Ensures (modPeerTimer site pid timer delay) (fun w => w.k.wg = some d)
      (fun ok w => ok = (d.running && !p.isDead) ∧
        if ok then ∃ expiry, peerAt w pid = some (p.setTimer timer (some expiry))
        else peerAt w pid = some p) :=
  modPeerTimer_effect site pid timer delay d p resident

/-- The traversal hook re-arms persistent keepalive exactly when its interval is nonzero and the device is running and peer alive. -/
theorem original_traversal (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (timersTraversal pid) (fun w => w.k.wg = some d)
      (fun _ w => if p.persistentKeepaliveInterval ≠ 0 ∧ d.running = true ∧ p.isDead = false
        then ∃ expiry, peerAt w pid = some (p.setTimer .persistentKeepalive (some expiry))
        else peerAt w pid = some p) :=
  timersTraversal_effect pid d p resident

/-- The session-derived hook re-arms only the zero-key timer when running and alive, and otherwise preserves the peer. -/
theorem original_session_derived (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (timersSessionDerived pid) (fun w => w.k.wg = some d)
      (fun _ w => if d.running && !p.isDead
        then ∃ expiry, peerAt w pid = some (p.setTimer .zeroKeyMaterial (some expiry))
        else peerAt w pid = some p) :=
  timersSessionDerived_effect pid d p resident

/-- Data receipt while running arms an absent keepalive timer on a live peer, or requests another keepalive when the timer is already pending. -/
theorem original_data_received (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (timersDataReceived pid) (fun w => w.k.wg = some d)
      (fun _ w => if d.running then
        if p.timerPending .sendKeepalive then
          peerAt w pid = some { p with timerNeedAnotherKeepalive := true }
        else if p.isDead then peerAt w pid = some p
        else ∃ expiry, peerAt w pid = some (p.setTimer .sendKeepalive (some expiry))
        else peerAt w pid = some p) :=
  timersDataReceived_effect pid d p resident

/-- Handshake completion deletes the retransmit timer, resets attempts and the last-minute flag, and records the wall-clock bytes; other peer fields are preserved. -/
theorem original_handshake_complete (pid : PeerId) (site : HiddenSite) (p : Peer) :
    Ensures (timersHandshakeComplete pid site) (fun w => peerAt w pid = some p)
      (fun _ w => ∃ now, peerAt w pid = some
        { (p.setTimer .retransmitHandshake none) with
          timerHandshakeAttempts := 0, sentLastminuteHandshake := false, walltimeLastHandshake := now }) :=
  timersHandshakeComplete_effect pid site p

/-- Every successful jitter draw returns fewer than HZ/3 ticks and leaves
all kernel state unchanged; exhausted record streams do not return a value. -/
theorem original_jitter_bound (site : HiddenSite) (initial : Kernel) :
    Ensures (jitterBelowRekeyTimeout site) (fun w => w.k = initial)
      (fun n w => w.k = initial ∧ n < HZ / 3) :=
  (ensures_iff _ _ _).mpr (jitter_bounded (· = initial) site)

/-- The authenticated-send hook deletes only the send-keepalive timer. -/
theorem original_authenticated_sent (pid : PeerId) (p : Peer) :
    Ensures (timersAnyAuthenticatedPacketSent pid) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (p.setTimer .sendKeepalive none)) :=
  delTimer_exact pid .sendKeepalive p

/-- The authenticated-receive hook deletes only the new-handshake timer. -/
theorem original_authenticated_received (pid : PeerId) (p : Peer) :
    Ensures (timersAnyAuthenticatedPacketReceived pid) (fun w => peerAt w pid = some p)
      (fun _ w => peerAt w pid = some (p.setTimer .newHandshake none)) :=
  delTimer_exact pid .newHandshake p

end Leanux.Proofs.WG.TimerDiscipline
