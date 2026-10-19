import Leanux.Proofs.WG.TransmitSecurity.StagedTimerFrames

/-! Staged provenance is unchanged by native timer metadata and clock bookkeeping. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem exact_ring {action : WG.M α} (epoch : SameView RxRing.nativeCell action)
    (queues : SameView stagedAt action) : Preserves (Inv h) action :=
  frame (epoch_rx_ring epoch) (Staged.of_view _ queues)

theorem arm (pid : PeerId) (timer : PeerTimer) (delay : Nat) (jc : Option UInt64) :
    Preserves (Inv h) (armTimer pid timer delay jc) :=
  exact_ring (RxRing.armTimer_cell pid timer delay jc) (Exact.arm pid timer delay jc)

theorem delete_timer (pid : PeerId) (timer : PeerTimer) : Preserves (Inv h) (delTimer pid timer) :=
  exact_ring (RxRing.delTimer_cell pid timer) (Exact.delete_timer pid timer)

theorem timer_guard (pid : PeerId) : Preserves (Inv h) (modPeerTimerGuard pid) :=
  exact_ring (RxRing.modPeerTimerGuard_cell pid) (Exact.timer_guard pid)

theorem modify_timer (site : HiddenSite) (pid : PeerId) (timer : PeerTimer) (delay : Nat) :
    Preserves (Inv h) (modPeerTimer site pid timer delay) :=
  exact_ring (RxRing.modPeerTimer_cell site pid timer delay) (Exact.modify_timer site pid timer delay)

theorem data_sent (pid : PeerId) : Preserves (Inv h) (timersDataSent pid) :=
  exact_ring (RxRing.timersDataSent_cell pid) (Exact.data_sent pid)

theorem data_received (pid : PeerId) : Preserves (Inv h) (timersDataReceived pid) :=
  exact_ring (RxRing.timersDataReceived_cell pid) (Exact.data_received pid)

theorem handshake_complete (pid : PeerId) (site : HiddenSite) :
    Preserves (Inv h) (timersHandshakeComplete pid site) :=
  exact_ring (RxRing.timersHandshakeComplete_cell pid site) (Exact.handshake_complete pid site)

theorem session_derived (pid : PeerId) : Preserves (Inv h) (timersSessionDerived pid) :=
  exact_ring (RxRing.timersSessionDerived_cell pid) (Exact.session_derived pid)

theorem traversal (pid : PeerId) : Preserves (Inv h) (timersTraversal pid) :=
  exact_ring (RxRing.timersTraversal_cell pid) (Exact.traversal pid)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
