import Leanux.Proofs.WG.RetirementSecurity.TxSuspensionTransmit

/-! Exact native RX poll frames retain suspended scheduler records. Its GRO
callback is the only open product action, with a concrete suspension contract. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxSuspension
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem rx_packet (skb : SkbId) : Keeps (getRxSkb skb) := by
  apply skb_lift
  suspension_source [SkbStore.getRx] using [invariant]

theorem free_rx (skb : SkbId) : Keeps (freeRxSkb skb) := by
  apply skb_lift
  suspension_source [SkbStore.freeRx,SkbStore.getRx] using [invariant]

theorem rx_counter (kid : KeypairId) (nonce : Nat) : Keeps (counterValidate kid nonce) := by
  suspension_source [counterValidate,WG.orM] using [key,set_key,branch,compare,invariant]

theorem prev_peek {α : Type} (q : PrevQueue α) : Keeps q.peek := by
  suspension_source [PrevQueue.peek,PrevQueue.dequeue] using [branch,compare,invariant,unsupported]

theorem rx_peek (pid : PeerId) : Keeps (peekRxQueue pid) := by
  suspension_source [peekRxQueue] using [peer,set_peer,prev_peek]

theorem rx_drop (pid : PeerId) : Keeps (dropRxQueue pid) := by
  suspension_source [dropRxQueue] using [peer,set_peer]

theorem rx_complete (pid : PeerId) : Keeps (completeRxQueue pid) := by
  suspension_source [completeRxQueue] using [peer,set_peer]

theorem endpoint_from (src : SkbSource) : Keeps (endpointFromSkb src) := by
  suspension_source [endpointFromSkb] using [branch,invariant,unsupported]

theorem product_branch (decision : Decision) (value : Bool) :
    SameView suspended (Leanux.branch decision value : Leanux.M Bool) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run
  rfl

theorem product_invariant {α : Type} (why : String) :
    SameView suspended (Leanux.invariant why : Leanux.M α) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run

theorem product_unsupported {α : Type} (why : String) :
    SameView suspended (Leanux.unsupported why : Leanux.M α) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w result v run
  cases run

theorem gro_receive (callback : List (List UInt8)→Leanux.M Unit)
    (keeps : ∀xs,SameView suspended (callback xs)) (gro : GroState) (pkt : List UInt8) :
    SameView suspended (napiGroReceive callback gro pkt) := by
  intro initial
  let P:=fun w=>suspended w=initial
  have call (xs : List (List UInt8)) : Preserves P (callback xs) := keeps xs initial
  have stopped {α : Type} (why : String) : Preserves P (Leanux.unsupported why : Leanux.M α) :=
    product_unsupported why initial
  change Preserves P _
  routing_tx_source [napiGroReceive,groNormalOne,groNormalList] using [call,stopped]

theorem gro_flush (callback : List (List UInt8)→Leanux.M Unit)
    (keeps : ∀xs,SameView suspended (callback xs)) (gro : GroState) :
    SameView suspended (napiGroFlushAll callback gro) := by
  intro initial
  let P:=fun w=>suspended w=initial
  have call (xs : List (List UInt8)) : Preserves P (callback xs) := keeps xs initial
  change Preserves P _
  routing_tx_source [napiGroFlushAll,groNormalOne,groNormalList] using [call]

theorem rx_poll (pid budget : Nat) (callback : List (List UInt8)→Leanux.M Unit)
    (keeps : ∀xs,SameView suspended (callback xs)) : SameView suspended (rxPoll pid budget callback) := by
  rw [←rxPollGrouped_eq]
  intro initial
  let P:=fun w=>suspended w=initial
  have gro (g : GroState) (pkt : List UInt8) : Preserves P (napiGroReceive callback g pkt) :=
    gro_receive callback keeps g pkt initial
  have flush (g : GroState) : Preserves P (napiGroFlushAll callback g) := gro_flush callback keeps g initial
  have decision (which : Decision) (value : Bool) : Preserves P (Leanux.branch which value : Leanux.M Bool) :=
    product_branch which value initial
  have failed {α : Type} (why : String) : Preserves P (Leanux.invariant why : Leanux.M α) :=
    product_invariant why initial
  have stopped {α : Type} (why : String) : Preserves P (Leanux.unsupported why : Leanux.M α) :=
    product_unsupported why initial
  change Preserves P _
  unfold rxPollGrouped WG.andM
  repeat' first
    | env_operation_fact gro
    | env_operation_fact flush
    | env_operation_fact decision
    | env_operation_fact failed
    | env_operation_fact stopped
    | (allocation_release_lift_from WG.M
       apply (product ?_) initial
       simp only [monadLift_self]
       suspension_source [] using [rx_peek,rx_drop,rx_complete,rx_counter,receive_done,rx_packet,
         free_rx,peer_put,key_put,endpoint_from,branch,invariant,unsupported])
    | (rx_retention_head ForIn.forIn
       first
         | (apply list_view_spec id P
            intro x state
            change Preserves P _)
         | rw [Std.Legacy.Range.forIn_eq_forIn_range'])
    | routing_tx_step

end Leanux.Proofs.WG.RetirementSecurity.TxSuspension
