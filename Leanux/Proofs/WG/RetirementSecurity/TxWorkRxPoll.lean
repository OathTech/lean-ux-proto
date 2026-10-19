import Leanux.Proofs.WG.RetirementSecurity.TxWorkRxCompletion

/-! Original RX poll transport for the joint physical coverage and TX service
carrier. Callback service is explicit here; native stack callbacks are the next
composition cut. Ambient changes are harmless only for this fixed actor list. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem serving_join {action : WG.M α}
    (service : Preserves (Obligations crypt tx) action)
    (covered : Preserves (Covered locals crypt) action) : Preserves (Serving locals crypt tx) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨(hoare_iff_run_ambient _ _ _).mp service w a result v b before.1 run,
    (hoare_iff_run_ambient _ _ _).mp covered w a result v b before.2 run⟩

theorem serving_store {action : WG.M α} (same : SameWGStore action) :
    Preserves (Serving locals crypt tx) action :=
  serving_join (passive (cryptWire_store same) (ownership_queues (ownershipPoints_kernel _ same)) (store same))
    (TxCovered.Native.coherent_store same)

theorem serving_key_put (kid : Option KeypairId) (now : Bool) :
    Preserves (Serving locals crypt tx) (keypairPut kid now) := by
  apply serving_join
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact before.key_put kid now a b run
  · exact TxCovered.join (RxPollOccurrences.key_put kid now) (TxCoveragePoll.key_put kid now)

theorem serving_peer_put (pid : Option PeerId) : Preserves (Serving locals crypt tx) (peerPut pid) := by
  apply serving_join
  · apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact before.peer_put pid a b run
  · exact TxCovered.Native.peer_put pid

theorem peek_rx_work (pid : PeerId) : SameView queued (peekRxQueue pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact (store (prevQueuePeek_sameWGStore _)).wp (·=initial))
    | tx_work_step initial

theorem drop_rx_work (pid : PeerId) : SameView queued (dropRxQueue pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold dropRxQueue
  repeat' tx_work_step initial

theorem complete_rx_work (pid : PeerId) : SameView queued (completeRxQueue pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold completeRxQueue
  repeat' tx_work_step initial

theorem counter_work (kid : KeypairId) (nonce : Nat) : SameView queued (counterValidate kid nonce) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w=>queued w=initial)
       intro x state
       change Preserves (fun w=>queued w=initial) _)
    | tx_work_step initial

theorem skb_work (action : SkbM α) : SameView queued (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d packetStore before device
  simpa only [queued,device,Option.map_some,Option.getD_some] using before

theorem serving_peek_rx (pid : PeerId) : Preserves (Serving locals crypt tx) (peekRxQueue pid) :=
  serving_join (passive (RxPollOccurrences.peek_wire pid) (RxPollOccurrences.peek_queues pid) (peek_rx_work pid))
    (TxCovered.join (RxPollOccurrences.peek pid) (TxCoveragePoll.peek pid))

theorem serving_drop_rx (pid : PeerId) : Preserves (Serving locals crypt tx) (dropRxQueue pid) :=
  serving_join (passive (RxPollOccurrences.drop_wire pid) (RxPollOccurrences.drop_queues pid) (drop_rx_work pid))
    (TxCovered.join (RxPollOccurrences.drop pid) (TxCoveragePoll.drop pid))

theorem serving_complete_rx (pid : PeerId) : Preserves (Serving locals crypt tx) (completeRxQueue pid) :=
  serving_join (passive (RxPollOccurrences.complete_wire pid) (RxPollOccurrences.complete_queues pid) (complete_rx_work pid))
    (TxCovered.join (RxPollOccurrences.complete pid) (TxCoveragePoll.complete pid))

theorem serving_counter (kid : KeypairId) (nonce : Nat) :
    Preserves (Serving locals crypt tx) (counterValidate kid nonce) :=
  serving_join (passive (RxPollOccurrences.counter_wire kid nonce) (RxPollOccurrences.counter_queues kid nonce)
    (counter_work kid nonce)) (TxCovered.join (RxPollOccurrences.counter kid nonce) (TxCoveragePoll.counter kid nonce))

theorem serving_free_rx (skb : SkbId) : Preserves (Serving locals crypt tx) (freeRxSkb skb) :=
  serving_join (passive (ReceiveOccurrences.free_rx_wire skb) (ReceiveOccurrences.skb_queues _) (skb_work _))
    (TxCovered.join (RxPollOccurrences.free_rx skb) (TxCoveragePoll.free_rx skb))

theorem serving_poll (pid budget : Nat) (callback : List (List UInt8)→Leanux.M Unit)
    (hc : ∀xs,Preserves (fun w:World=>Serving locals crypt tx w.wg) (callback xs)) :
    Preserves (fun w:World=>Serving locals crypt tx w.wg) (rxPoll pid budget callback) := by
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
       apply PublicationPoll.native_product (Serving locals crypt tx)
       simp only [monadLift_self]
       repeat' first
         | (rx_retention_head peekRxQueue; exact serving_peek_rx _)
         | (rx_retention_head dropRxQueue; exact serving_drop_rx _)
         | (rx_retention_head completeRxQueue; exact serving_complete_rx _)
         | (rx_retention_head counterValidate; exact serving_counter _ _)
         | (rx_retention_head WG.consumeDataDone; exact serving_receive_done _ _ _)
         | (rx_retention_head getRxSkb; exact ReceiveOccurrences.get_rx _ _)
         | (rx_retention_head freeRxSkb; exact serving_free_rx _)
         | (rx_retention_head WG.peerPut; exact serving_peer_put _)
         | (rx_retention_head keypairPut; exact serving_key_put _ _)
         | (rx_retention_head endpointFromSkb; exact serving_store (endpointFromSkb_sameWGStore _))
         | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
         | rx_retention_step)
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ hi=>hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w:World=>Serving locals crypt tx w.wg)
       intro x state
       change Preserves (fun w:World=>Serving locals crypt tx w.wg) _)
    | rx_retention_step

end Leanux.Proofs.WG.RetirementSecurity.TxWork
