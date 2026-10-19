import Leanux.Proofs.WG.TransmitSecurity.BatchNativeReceive

/-! RX polling preserves batch coherence across authenticated promotion,
GRO callbacks, replay-counter updates and reference release. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Poll
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open RetirementSecurity Queues.RxCredits Native

theorem store {native : WG.M α} (same : SameWGStore native) :
    Preserves (Coherent locals active) native := coherent_store same

theorem peek (pid : PeerId) : Preserves (Coherent locals active) (peekRxQueue pid) :=
  coherent_join (RxPollOccurrences.peek pid) (wire (RxPollOccurrences.peek_queues pid) (RxPollOccurrences.peek_wire pid))

theorem drop (pid : PeerId) : Preserves (Coherent locals active) (dropRxQueue pid) :=
  coherent_join (RxPollOccurrences.drop pid) (wire (RxPollOccurrences.drop_queues pid) (RxPollOccurrences.drop_wire pid))

theorem complete (pid : PeerId) : Preserves (Coherent locals active) (completeRxQueue pid) :=
  coherent_join (RxPollOccurrences.complete pid) (wire (RxPollOccurrences.complete_queues pid) (RxPollOccurrences.complete_wire pid))

theorem counter (kid : KeypairId) (nonce : Nat) : Preserves (Coherent locals active) (counterValidate kid nonce) :=
  coherent_join (RxPollOccurrences.counter kid nonce) (wire (RxPollOccurrences.counter_queues kid nonce) (RxPollOccurrences.counter_wire kid nonce))

theorem free_rx (id : SkbId) : Preserves (Coherent locals active) (freeRxSkb id) :=
  coherent_join (RxPollOccurrences.free_rx id) (wire (ReceiveOccurrences.skb_queues _) (ReceiveOccurrences.free_rx_wire id))

theorem key_put (id : Option KeypairId) (now : Bool) :
    Preserves (Coherent locals active) (keypairPut id now) :=
  coherent_join (RxPollOccurrences.key_put id now) (Native.key_put id now)

theorem peer_put (id : Option PeerId) : Preserves (Coherent locals active) (peerPut id) :=
  coherent_join (RxPollOccurrences.peer_put id) (Native.peer_put id)

/-- The original product callback remains arbitrary with its exact head and
allocation-state contract. All poll budgets and normal failure branches remain. -/
theorem poll (pid budget : Nat)
    (callback : List (List UInt8)→Leanux.M Unit)
    (hc : ∀xs,Preserves (fun w:World=>Coherent locals active w.wg) (callback xs)) :
    Preserves (fun w:World=>Coherent locals active w.wg) (rxPoll pid budget callback) := by
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
       apply PublicationPoll.native_product (Coherent locals active)
       simp only [monadLift_self]
       repeat' first
         | (rx_retention_head peekRxQueue; exact peek _)
         | (rx_retention_head dropRxQueue; exact drop _)
         | (rx_retention_head completeRxQueue; exact complete _)
         | (rx_retention_head counterValidate; exact counter _ _)
         | (rx_retention_head WG.consumeDataDone; exact consume _ _ _)
         | (rx_retention_head getRxSkb; exact ReceiveOccurrences.get_rx _ _)
         | (rx_retention_head freeRxSkb; exact free_rx _)
         | (rx_retention_head WG.peerPut; exact peer_put _)
         | (rx_retention_head keypairPut; exact key_put _ _)
         | (rx_retention_head endpointFromSkb
            exact store (endpointFromSkb_sameWGStore _))
         | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
         | rx_retention_step)
    | (allocation_release_lift_from AmbientM; exact productAmbient_spec _ _ (fun _ _ hi=>hi))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w:World=>Coherent locals active w.wg)
       intro x b
       change Preserves (fun w:World=>Coherent locals active w.wg) _)
    | rx_retention_step

theorem stack (pid budget : Nat) :
    Preserves (fun w:World=>Coherent locals active w.wg)
      (rxPoll pid budget (fun packets=>packets.forM Env.deliverInner)) :=
  poll pid budget _ Stack.stackForM_stack

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Poll
