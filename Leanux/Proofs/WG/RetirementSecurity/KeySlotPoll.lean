import Leanux.Proofs.WG.RetirementSecurity.KeySlotStack
import Leanux.Proofs.WG.RetirementSecurity.RxPollOccurrences

/-! Native RX polling retains live key slots through authenticated completion,
queue bookkeeping, reference payment and the actual stack callback. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open Queues.RxCredits

theorem poll_peek (pid : PeerId) : Preserves (InvExcept pending) (peekRxQueue pid) := by
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact store (prevQueuePeek_sameWGStore _))
    | key_slot_rx_step

theorem poll_drop (pid : PeerId) : Preserves (InvExcept pending) (dropRxQueue pid) := by
  unfold dropRxQueue
  repeat' key_slot_rx_step

theorem poll_complete (pid : PeerId) : Preserves (InvExcept pending) (completeRxQueue pid) := by
  unfold completeRxQueue
  repeat' key_slot_rx_step

theorem poll (pid budget : Nat)
    (callback : List (List UInt8)→Leanux.M Unit)
    (hc : ∀xs,Preserves (fun w:World=>InvExcept pending w.wg) (callback xs)) :
    Preserves (fun w:World=>InvExcept pending w.wg) (rxPoll pid budget callback) := by
  rw [←rxPollGrouped_eq]
  unfold rxPollGrouped
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,invariant,unsupported,WG.andM]
  repeat' first
    | (rx_retention_head napiGroReceive
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groReceive_preserves)
         _ callback hc _ _)
    | (rx_retention_head napiGroFlushAll
       exact (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPoll.«0».Leanux.Proofs.WG.CurrentPoll.groFlush_preserves)
         _ callback hc _)
    | (allocation_release_lift_from WG.M
       apply PublicationPoll.native_product (InvExcept pending)
       simp only [monadLift_self]
       repeat' first
         | (rx_retention_head peekRxQueue; exact poll_peek _)
         | (rx_retention_head dropRxQueue; exact poll_drop _)
         | (rx_retention_head completeRxQueue; exact poll_complete _)
         | (rx_retention_head counterValidate; exact validate_counter _ _)
         | (rx_retention_head WG.consumeDataDone; exact consume_done _ _ _)
         | (rx_retention_head getRxSkb; exact ReceiveOccurrences.get_rx _ _)
         | (rx_retention_head freeRxSkb; unfold freeRxSkb; exact skb _)
         | (rx_retention_head WG.peerPut; exact peer_put _)
         | (rx_retention_head keypairPut; exact key_put _ _)
         | (rx_retention_head endpointFromSkb
            exact store (endpointFromSkb_sameWGStore _))
         | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
         | rx_retention_step)
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ hi=>hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w:World=>InvExcept pending w.wg)
       intro x b
       change Preserves (fun w:World=>InvExcept pending w.wg) _)
    | rx_retention_step

theorem stack (pid budget : Nat) :
    Preserves (fun w:World=>InvExcept pending w.wg)
      (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) :=
  poll pid budget _ stackForM_stack

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
