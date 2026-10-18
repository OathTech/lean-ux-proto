import Leanux.Proofs.WG.Noise.PendingTicketRemovalFrames
import Leanux.Proofs.WG.Noise.PendingControlSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Lifetimes Leanux.Proofs.Framing Leanux.Proofs.Logged
open Queues

theorem clear_worker (pid : PeerId) (seen : List Nat) : Preserves (fun w => NativeInv w seen) (queuedExpiredZeroKeyMaterial pid) :=
  PendingReception.native_preserves _ (ConfiguredRemoval.queuedClear pid)
    (CurrentSlots.Removal.queuedClear pid) (PendingTickets.queuedExpiredZeroKeyMaterial_retained pid) seen

theorem send_worker (pid : PeerId) (seen : List Nat) : Preserves (fun w => NativeInv w seen) (handshakeSendWorker pid) :=
  PendingReception.native_preserves _ (ConfiguredRemoval.handshakeWorker pid)
    (CurrentSlots.Removal.handshakeWorker pid) (PendingTickets.handshakeSendWorker_retained pid) seen

theorem flushed_send (pid : PeerId) (seen : List Nat) : Preserves (fun w => NativeInv w seen) (runFlushedSendWork pid) :=
  PendingReception.native_preserves _ (ConfiguredRemoval.flushedSend pid)
    (CurrentSlots.Removal.flushedSend pid) (PendingTickets.runFlushedSendWork_retained pid) seen

theorem flushed_clear (pid : PeerId) (seen : List Nat) : Preserves (fun w => NativeInv w seen) (runFlushedClearWork pid) :=
  PendingReception.native_preserves _ (ConfiguredRemoval.flushedClear pid)
    (CurrentSlots.Removal.flushedClear pid) (PendingTickets.runFlushedClearWork_retained pid) seen

theorem stop_timers (pid : PeerId) (seen : List Nat) : Preserves (fun w => NativeInv w seen) (timersStop pid) :=
  PendingReception.native_preserves _ (ConfiguredRemoval.stopTimers pid)
    (CurrentSlots.Removal.stopTimers pid) (PendingTickets.timersStop_retained pid) seen

theorem remove_after_dead (pid : PeerId) (seen : List Nat) : Preserves (fun w => NativeInv w seen) (peerRemoveAfterDead pid) :=
  PendingReception.native_preserves _ (ConfiguredRemoval.afterDead pid)
    (CurrentSlots.Removal.afterDead pid) (PendingTickets.peerRemoveAfterDead_retained pid) seen

theorem drain (upTo : Option PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (drainHandshakeSendWq upTo) :=
  PendingReception.native_preserves _ (ConfiguredRemoval.drain upTo)
    (CurrentSlots.Removal.drain upTo) (PendingTickets.drainHandshakeSendWq_retained upTo) seen

theorem remove (peer : Option PeerId) (seen : List Nat) : Preserves (fun w => NativeInv w seen) (peerRemove peer) :=
  PendingReception.native_preserves _ (ConfiguredRemoval.remove peer)
    (CurrentSlots.Removal.remove peer) (PendingTickets.peerRemove_retained peer) seen

theorem remove_all (seen : List Nat) : Preserves (fun w => NativeInv w seen) peerRemoveAll :=
  PendingReception.native_preserves _ ConfiguredRemoval.removeAll
    CurrentSlots.Removal.removeAll PendingTickets.peerRemoveAll_retained seen

theorem clear_worker_observed (pid : PeerId) : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver (queuedExpiredZeroKeyMaterialPrefix pid))) :=
  lifecycle_observed _ _ (queuedExpiredZeroKeyMaterialPrefix_erases pid) (clear_worker pid)

theorem send_worker_observed (pid : PeerId) : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver (handshakeSendWorkerPrefix pid))) :=
  lifecycle_observed _ _ (handshakeSendWorkerPrefix_erases pid) (send_worker pid)

theorem flushed_send_observed (pid : PeerId) : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver (runFlushedSendWorkPrefix pid))) :=
  lifecycle_observed _ _ (runFlushedSendWorkPrefix_erases pid) (flushed_send pid)

theorem flushed_clear_observed (pid : PeerId) : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver (runFlushedClearWorkPrefix pid))) :=
  lifecycle_observed _ _ (runFlushedClearWorkPrefix_erases pid) (flushed_clear pid)

theorem stop_timers_observed (pid : PeerId) : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver (timersStopPrefix pid))) :=
  lifecycle_observed _ _ (timersStopPrefix_erases pid) (stop_timers pid)

theorem remove_after_dead_observed (pid : PeerId) : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver (peerRemoveAfterDeadPrefix pid))) :=
  lifecycle_observed _ _ (peerRemoveAfterDeadPrefix_erases pid) (remove_after_dead pid)

theorem drain_observed (upTo : Option PeerId) : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver (drainHandshakeSendWqPrefix upTo))) :=
  lifecycle_observed _ _ (drainHandshakeSendWqPrefix_erases upTo) (drain upTo)

theorem remove_observed (peer : Option PeerId) : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver (peerRemovePrefix peer))) :=
  lifecycle_observed _ _ (peerRemovePrefix_erases peer) (remove peer)

theorem remove_all_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver peerRemoveAllPrefix)) :=
  lifecycle_observed _ _ peerRemoveAllPrefix_erases remove_all

end Leanux.Proofs.WG.Noise.PendingSession
