import Leanux.Proofs.WG.TimerDiscipline.RetryGiveUpSource
import Leanux.Proofs.WG.TimerDiscipline.Model
import Leanux.Proofs.WG.TimerDiscipline.View
import Leanux.Proofs.WG.TimerDiscipline.ArmingSource
import Leanux.Proofs.WG.Config.QueuedHandshake
import Leanux.Proofs.WG.Config.EndpointSources

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.TimerDiscipline
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Leanux.Proofs.WG.Config Std.Do

/-- Retry variant of Config.queuedReadPrefix: retain the original false
queuedNotRetry decision and do not reset the attempt counter. -/
def retryReadPrefix (pid : PeerId) : M Peer := do
  requireNotPending pid "queueing a handshake"
  _ ← branch .queuedNotRetry false
  getPeer pid

theorem sendQueuedRetry_factor (pid : PeerId) :
    sendQueuedHandshakeInitiation pid true = (do
      let p ← retryReadPrefix pid
      let now ← hiddenClock64 .birthdateExpired
      queuedAfterClock pid p now) := by
  simp [sendQueuedHandshakeInitiation, retryReadPrefix, queuedAfterClock,
    branchExpired, birthdateTest, branch, bind_assoc]

theorem retryReadPrefix_returns (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Returns (retryReadPrefix pid) (fun w => w.k.wg = some d)
      (fun result w => result = p ∧ w.k.wg = some d) := by
  rw [returns_iff]
  mvcgen [retryReadPrefix, requireNotPending, branch, getPeer, getDev, getK, invariant]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals grind only

theorem sendQueuedRetry_exact (pid : PeerId) (d : Device) (p : Peer)
    (resident : d.peers[pid]? = some p) :
    Ensures (sendQueuedHandshakeInitiation pid true) (fun w => w.k.wg = some d)
      (fun _ w => ∃ now, w.k.wg = some (queuedDevice d pid p now)) := by
  intro w ret v hp run
  cases ret
  obtain ⟨result, before, hprefix, value, hdevice⟩ := retryReadPrefix_returns pid d p resident w hp
  subst result
  rw [sendQueuedRetry_factor, StateT.run_bind, hprefix] at run
  change ((hiddenClock64 .birthdateExpired).run before >>= fun out =>
    (queuedAfterClock pid p out.1).run out.2) = .ok ((), v) at run
  cases hclock : (hiddenClock64 .birthdateExpired).run before with
  | error err => rw [hclock] at run; cases run
  | ok pair =>
    obtain ⟨now, after⟩ := pair
    rw [hclock] at run
    have hafter := (ensures_iff _ _ _).mpr
      (hiddenClock64_kernel_spec (fun k => k.wg = some d) .birthdateExpired)
      before now after hdevice hclock
    exact ⟨now, queuedAfterClock_exact pid d p now resident after () v hafter run⟩

def retryAt (w : World) (pid : PeerId) : Option RetryView :=
  (peerAt w pid).map retryView


end Leanux.Proofs.WG.TimerDiscipline
