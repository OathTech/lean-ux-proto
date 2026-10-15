import Leanux.Proofs.WG.Config.QuietModel

/-! Existing preservation support, separated from state-changing effects. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem deleteTimers_withoutPeers (ts : List PeerTimer) (d : Device) (pid : PeerId) (p : Peer) :
    withoutPeers (deleteTimersDevice ts d pid p) = withoutPeers d := by
  induction ts generalizing d p with
  | nil => rfl
  | cons t ts ih => exact ih _ _

theorem quietCleanup_frame (d : Device) (pid : PeerId) (p : Peer) :
    withoutPeers (quietCleanupDevice d pid p) = withoutPeers d :=
  deleteTimers_withoutPeers _ _ _ _

theorem quietCleanup_refcount (p : Peer) : (quietCleanupPeer p).refcount = p.refcount := by
  simp [quietCleanupPeer, deleteTimersPeer, PeerTimer.all, Peer.setTimer, emptyKeysPeer]

end Leanux.Proofs.WG.Config
