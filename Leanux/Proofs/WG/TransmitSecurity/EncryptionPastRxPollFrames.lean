import Leanux.Proofs.WG.TransmitSecurity.EncryptionPastReceive
import Leanux.Proofs.WG.Queues.TxLivePoll

/-! Native receive-poll bookkeeping cannot republish an old encryption alias.
RX packet deletion preserves the independent physical TX ring refinement. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TxDisposition
set_option maxHeartbeats 600000

theorem ready_peek_rx (pid : PeerId) : Preserves (Ready past active) (peekRxQueue pid) := by
  unfold peekRxQueue
  repeat' first
    | (rx_retention_head PrevQueue.peek; exact ready_store (prevQueuePeek_sameWGStore _))
    | encryption_past_receive_step

theorem ready_drop_rx (pid : PeerId) : Preserves (Ready past active) (dropRxQueue pid) := by
  unfold dropRxQueue
  repeat' encryption_past_receive_step

theorem ready_complete_rx (pid : PeerId) : Preserves (Ready past active) (completeRxQueue pid) := by
  unfold completeRxQueue
  repeat' encryption_past_receive_step

theorem ready_counter (kid nonce : Nat) : Preserves (Ready past active) (counterValidate kid nonce) := by
  unfold counterValidate WG.orM
  simp (config := {zeta := false}) only [Std.Legacy.Range.forIn_eq_forIn_range',branch,branchCmp,invariant]
  repeat' encryption_past_receive_step

theorem ready_get_rx (id : SkbId) : Preserves (Ready past active) (getRxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (Packets.getRxSkb_current id w v result a b run).1 ▸ before

theorem ready_free_rx (id : SkbId) : Preserves (Ready past active) (freeRxSkb id) :=
  ready_frame ((pinned_const _private.Leanux.Proofs.WG.Queues.TxLivePoll.«0».Leanux.Proofs.WG.Queues.TxDisposition.LivePoll.freeRx) id)
    (free_rx id)

end Leanux.Proofs.WG.TransmitSecurity.EncryptionPast
