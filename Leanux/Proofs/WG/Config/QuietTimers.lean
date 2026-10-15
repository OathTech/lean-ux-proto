import Leanux.Proofs.WG.Config.QuietFrames
import Leanux.Proofs.WG.Config.EmptyKeypairs

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

theorem delTimer_returns (pid : PeerId) (t : PeerTimer) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (delTimer pid t) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (withPeer d pid (p.setTimer t none))) := by
  rw [returns_iff]
  mvcgen [delTimer, getPeer, getDev, getK, setPeer, modifyDev, modifyK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all only [Option.map_some, Option.some.injEq]
  all_goals subst_vars
  all_goals simp_all [withPeer]

theorem deleteTimers_returns (ts : List PeerTimer) (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (forIn ts PUnit.unit (fun t _ => do delTimer pid t; pure (.yield PUnit.unit))) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (deleteTimersDevice ts d pid p)) := by
  induction ts generalizing d p with
  | nil => intro w pre; exact ⟨(), w, rfl, pre⟩
  | cons t ts ih =>
    rw [List.forIn_cons]
    simp only [bind_assoc, pure_bind]
    exact returns_bind _ _ (delTimer_returns pid t d p resident)
      (fun _ => ih _ _ (by simp [withPeer]))

theorem timersStop_quiet_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) (quiet : d.clearWorkQueue = []) :
    Returns (timersStop pid) (fun w => w.k.wg = some d)
      (fun _ w => w.k.wg = some (deleteTimersDevice PeerTimer.all d pid p)) := by
  have hqueue : (deleteTimersDevice PeerTimer.all d pid p).clearWorkQueue = [] := by
    have h := congrArg Device.clearWorkQueue (deleteTimers_withoutPeers PeerTimer.all d pid p)
    exact h.trans quiet
  unfold timersStop
  refine returns_bind _ _ (deleteTimers_returns PeerTimer.all pid d p resident) ?_
  intro u
  rw [returns_iff]
  mvcgen [getDev, getK, invariant]
  all_goals simp_all

theorem drain_empty (upTo : Option PeerId) (d : Device) (w : World)
    (resident : w.k.wg = some d) (send : d.sendWorkQueue = []) (clear : d.clearWorkQueue = []) :
    (drainHandshakeSendWq upTo).run w = .ok ((), w) := by
  unfold drainHandshakeSendWq
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size]
  rw [List.range'_succ, List.forIn_cons]
  simp [getDev, getK, resident, send, clear, StateT.run, StateT.bind, StateT.pure, bind, pure, get, getThe, MonadStateOf.get, StateT.get, Except.bind, Except.pure]

end Leanux.Proofs.WG.Config
