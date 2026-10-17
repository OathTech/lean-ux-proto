import Leanux.Proofs.WG.Config.QuietFrames
import Leanux.Proofs.WG.Config.QuietDrainFrames
import Leanux.Proofs.WG.TimerDiscipline.ArmingClaims

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem deleteTimers_resident (ts : List PeerTimer) (d : Device) (pid : PeerId) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    (deleteTimersDevice ts d pid p).peers[pid]? = some (deleteTimersPeer ts p) := by
  induction ts generalizing d p with
  | nil => exact resident
  | cons t ts ih => exact ih _ _ (by simp [withPeer])

/-- Correct the former expiry-only prediction to include the actual wheel deletion. -/
theorem delTimer_returns (pid : PeerId) (t : PeerTimer) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (delTimer pid t) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (withPeer d pid ((p.setTimer t none).setWheel t none))) := by
  intro g ambient device
  have complete : ∃ value final after,
      ((delTimer pid t).run g).run ambient = .ok ((value, final), after) := by
    simp [delTimer, getPeer, getDev, device, resident, setPeer, modifyDev]
    exact ⟨_, _, _, rfl⟩
  obtain ⟨value, final, after, run⟩ := complete
  have effect := TimerDiscipline.delTimer_exact pid t p (Campaign2.snapshot g ambient)
    g ambient value final after ⟨rfl, by simpa [Campaign2.Snapshot.peerAt,
      Campaign2.snapshot, Campaign2.core, device] using resident⟩ run
  refine ⟨value, final, after, run, ?_⟩
  have changed := congrArg (fun s : Campaign2.Snapshot => s.wg.device) effect
  simpa [TimerDiscipline.delTimerView, Campaign2.snapshot, Campaign2.core, device, withPeer] using changed

theorem deleteTimers_returns (ts : List PeerTimer) (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (forIn ts PUnit.unit (fun t _ => do delTimer pid t; pure (.yield PUnit.unit)))
      (fun w => w.dev = some d)
      (fun _ w => w.dev = some (deleteTimersDevice ts d pid p)) := by
  induction ts generalizing d p with
  | nil => intro g ambient pre; exact ⟨(), g, ambient, rfl, pre⟩
  | cons t ts ih =>
    rw [List.forIn_cons]
    simp only [bind_assoc, pure_bind]
    exact returns_bind _ _ (delTimer_returns pid t d p resident)
      (fun _ => ih _ _ (by simp [withPeer]))

theorem timersStop_quiet_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (quiet : d.clearWorkQueue = []) :
    Returns (timersStop pid) (fun w => w.dev = some d)
      (fun _ w => w.dev = some (deleteTimersDevice PeerTimer.all d pid p)) := by
  have hqueue : (deleteTimersDevice PeerTimer.all d pid p).clearWorkQueue = [] := by
    have h := congrArg Device.clearWorkQueue (deleteTimers_withoutPeers PeerTimer.all d pid p)
    exact h.trans quiet
  unfold timersStop
  refine returns_bind _ _ (deleteTimers_returns PeerTimer.all pid d p resident) ?_
  intro _ g ambient device
  refine ⟨(), g, ambient, ?_, device⟩
  simp [getDev, device, hqueue]
  rfl

end Leanux.Proofs.WG.Config
