import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueueFramesNative
import Leanux.Proofs.WG.TransmitSecurity.StagedTimerOriginFrames

/-! Native timer metadata frames for the fixed staged ledger. These exact
footprints exclude timer callbacks which purge or release staged ownership. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.QueueNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

variable {history : List AuthenticatedEffects.CausalJournal.Event} {ledger : Ledger}

theorem exact_ring {action : WG.M α} (epoch : SameView RxRing.nativeCell action)
    (queues : SameView stagedAt action) : Preserves (QueueInv history ledger) action :=
  queue_frame (Origins.epoch_rx_ring epoch) queues

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64) :
    Preserves (QueueInv history ledger) (armTimer pid timer delay jc) :=
  exact_ring (RxRing.armTimer_cell pid timer delay jc) (Exact.arm pid timer delay jc)

theorem delete_timer (pid : PeerId) (timer : PeerTimer) :
    Preserves (QueueInv history ledger) (delTimer pid timer) :=
  exact_ring (RxRing.delTimer_cell pid timer) (Exact.delete_timer pid timer)

theorem timer_guard (pid : PeerId) : Preserves (QueueInv history ledger) (modPeerTimerGuard pid) :=
  exact_ring (RxRing.modPeerTimerGuard_cell pid) (Exact.timer_guard pid)

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (QueueInv history ledger) (modPeerTimer site pid timer delay) :=
  exact_ring (RxRing.modPeerTimer_cell site pid timer delay) (Exact.modify_timer site pid timer delay)

theorem data_sent (pid : PeerId) : Preserves (QueueInv history ledger) (timersDataSent pid) :=
  exact_ring (RxRing.timersDataSent_cell pid) (Exact.data_sent pid)

theorem data_received (pid : PeerId) : Preserves (QueueInv history ledger) (timersDataReceived pid) :=
  exact_ring (RxRing.timersDataReceived_cell pid) (Exact.data_received pid)

theorem handshake_complete (pid : PeerId) (site : HiddenSite) :
    Preserves (QueueInv history ledger) (timersHandshakeComplete pid site) :=
  exact_ring (RxRing.timersHandshakeComplete_cell pid site) (Exact.handshake_complete pid site)

theorem session_derived (pid : PeerId) : Preserves (QueueInv history ledger) (timersSessionDerived pid) :=
  exact_ring (RxRing.timersSessionDerived_cell pid) (Exact.session_derived pid)

theorem traversal (pid : PeerId) : Preserves (QueueInv history ledger) (timersTraversal pid) :=
  exact_ring (RxRing.timersTraversal_cell pid) (Exact.traversal pid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.QueueNative
