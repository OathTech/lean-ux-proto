import Leanux.Proofs.WG.RetirementSecurity.OccurrenceStack
import Leanux.Proofs.WG.Queues.TxRxHeadPoll

/-! The original RX poll bookkeeping and replay counter do not change TX
packet occurrences. Cached RX peeks remain separate from TX queue ownership. -/
namespace Leanux.Proofs.WG.RetirementSecurity.RxPollOccurrences
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open Queues.RxCredits

theorem peek_wire (pid : PeerId) : SameView txCryptWire (peekRxQueue pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek
       exact ((prevQueuePeek_sameWGStore _).of_factor
         (fun store => txCryptWire {dev := store.dev}) txCryptWire (fun _ => rfl)).wp (· = initial))
    | crypt_wire_step initial

theorem peek_queues (pid : PeerId) : SameView handoffTxView (peekRxQueue pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek
       exact ((prevQueuePeek_sameWGStore _).of_factor
         (fun store => handoffTxView {dev := store.dev}) handoffTxView (fun _ => rfl)).wp (· = initial))
    | crypt_queue_step initial

theorem peek_occurrences (pid : PeerId) : Preserves (TxOccurrences locals active) (peekRxQueue pid) :=
  occurrence_passive (peek_wire pid) (peek_queues pid)

theorem drop_wire (pid : PeerId) : SameView txCryptWire (dropRxQueue pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold dropRxQueue
  repeat' first
    | crypt_wire_step initial

theorem drop_queues (pid : PeerId) : SameView handoffTxView (dropRxQueue pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold dropRxQueue
  repeat' first
    | crypt_queue_step initial

theorem drop_occurrences (pid : PeerId) : Preserves (TxOccurrences locals active) (dropRxQueue pid) :=
  occurrence_passive (drop_wire pid) (drop_queues pid)

theorem complete_wire (pid : PeerId) : SameView txCryptWire (completeRxQueue pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold completeRxQueue
  repeat' first
    | crypt_wire_step initial

theorem complete_queues (pid : PeerId) : SameView handoffTxView (completeRxQueue pid) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold completeRxQueue
  repeat' first
    | crypt_queue_step initial

theorem complete_occurrences (pid : PeerId) : Preserves (TxOccurrences locals active) (completeRxQueue pid) :=
  occurrence_passive (complete_wire pid) (complete_queues pid)

theorem counter_wire (kid : KeypairId) (nonce : Nat) : SameView txCryptWire (counterValidate kid nonce) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,branchCmp,invariant]
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | crypt_wire_step initial

theorem counter_queues (kid : KeypairId) (nonce : Nat) : SameView handoffTxView (counterValidate kid nonce) := by
  intro initial
  change Preserves (fun w => handoffTxView w = initial) _
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,branchCmp,invariant]
  repeat' first
    | crypt_queue_step initial

theorem counter_occurrences (kid : KeypairId) (nonce : Nat) : Preserves (TxOccurrences locals active) (counterValidate kid nonce) :=
  occurrence_passive (counter_wire kid nonce) (counter_queues kid nonce)

end Leanux.Proofs.WG.RetirementSecurity.RxPollOccurrences
