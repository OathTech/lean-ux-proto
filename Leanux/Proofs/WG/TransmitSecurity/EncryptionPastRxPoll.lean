import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastRxPollFrames
import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastStack

/-! Full native RX polls preserve encryption-history exclusion through actual
GRO callbacks and reply staging. Logical pending aliases remain separate from
stale physical ring cells and from the active encryption batch. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition
set_option maxHeartbeats 600000

theorem rx_poll (pid budget : Nat) (callback : List (List UInt8) → Leanux.M Unit)
    (callbacks : ∀ packets, Preserves (fun w : World => Ready past active w.wg) (callback packets)) :
    Preserves (fun w : World => Ready past active w.wg) (rxPoll pid budget callback) := by
  rw [← rxPollGrouped_eq]
  unfold rxPollGrouped
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,invariant,unsupported,WG.andM]
  repeat' first
    | (rx_retention_head napiGroReceive
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
         _ callback callbacks _ _)
    | (rx_retention_head napiGroFlushAll
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
         _ callback callbacks _)
    | (allocation_release_lift_from WG.M
       apply PublicationPoll.native_product (Ready past active)
       simp only [monadLift_self]
       repeat' first
         | (rx_retention_head peekRxQueue; exact ready_peek_rx _)
         | (rx_retention_head dropRxQueue; exact ready_drop_rx _)
         | (rx_retention_head completeRxQueue; exact ready_complete_rx _)
         | (rx_retention_head counterValidate; exact ready_counter _ _)
         | (rx_retention_head WG.consumeDataDone; exact receive _ _ _)
         | (rx_retention_head getRxSkb; exact ready_get_rx _)
         | (rx_retention_head freeRxSkb; exact ready_free_rx _)
         | (rx_retention_head WG.peerPut; exact ready_frame (LiveFrontier.peer_put _) (peer_put _))
         | (rx_retention_head keypairPut; exact ready_frame (LiveFrontier.key_put _ _) (key_put _ _))
         | (rx_retention_head endpointFromSkb; exact ready_store (endpointFromSkb_sameWGStore _))
         | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
         | rx_retention_step)
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ before => before))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w : World => Ready past active w.wg)
       intro x b
       change Preserves (fun w : World => Ready past active w.wg) _)
    | rx_retention_step

theorem stack_poll (pid budget : Nat) :
    Preserves (fun w : World => Ready past active w.wg)
      (rxPoll pid budget (fun packets => packets.forM Env.deliverInner)) :=
  rx_poll pid budget _ stack

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
