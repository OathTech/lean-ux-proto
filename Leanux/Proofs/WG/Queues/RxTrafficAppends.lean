import Leanux.Proofs.WG.Queues.JointHistorySource
import Leanux.Proofs.WG.Queues.RxSyscallDispatchHistory

/-! Unconditional append behavior of the remaining actual RX syscall paths.
Every original incoming journal and every failed prefix is retained. -/
namespace Leanux.Proofs.WG.Queues.RxHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes

theorem pollScheduledInline_appends : Appends pollScheduledInline := by
  unfold pollScheduledInline RxNapi.inlineWith
  repeat' first
    | source_history_join
    | source_history_join_use
    | source_history_reduce
    | (rx_append_head ite; apply Appends.ite)
    | (rx_append_head observePoll; exact observePoll_appends _ _)
    | rx_append_step

theorem inject_appends (family port : Nat) (msg : List UInt8) (tos : Nat) (ll : Bool) (dest : Nat) :
    Appends (inject family port msg tos ll dest) := by
  unfold inject
  repeat' first
    | source_history_join
    | source_history_join_use
    | source_history_reduce
    | (rx_append_head ite; apply Appends.ite)
    | (rx_append_head runWorkerPrefix
       apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runWorker_appends))
    | (rx_append_head runCryptWorkers; exact runCryptWorkers_appends)
    | rx_append_step

theorem afterBatch_appends : Appends afterBatch := by
  unfold afterBatch
  repeat' first
    | source_history_join
    | source_history_join_use
    | source_history_reduce
    | (rx_append_head ite; apply Appends.ite)
    | (rx_append_head schedule; exact schedule_appends _)
    | (rx_append_head runCryptWorkers; exact runCryptWorkers_appends)
    | (rx_append_head runSendWorkers; exact runSendWorkers_appends)
    | rx_append_step

theorem flood_appends (count port family : Nat) (messages : List (List UInt8)) :
    Appends (flood count port family messages) := by
  unfold flood
  repeat' first
    | source_history_join
    | source_history_join_use
    | source_history_reduce
    | (rx_append_head ite; apply Appends.ite)
    | (rx_append_head runWorkerPrefix
       apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runWorker_appends))
    | (rx_append_head pollScheduledInline; exact pollScheduledInline_appends)
    | (rx_append_head afterBatch; exact afterBatch_appends)
    | rx_append_step

theorem batchItem_appends (d : Device) (cqes : List Int) (item : Env.BatchItem) :
    Appends (batchItem d cqes item) := by
  unfold batchItem
  repeat' first
    | source_history_join
    | source_history_join_use
    | source_history_reduce
    | (rx_append_head ite; apply Appends.ite)
    | (rx_append_head runWorkerPrefix
       apply (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runWorker_appends))
    | (rx_append_head pollScheduledInline; exact pollScheduledInline_appends)
    | rx_append_step

theorem batch_appends (items : List Env.BatchItem) : Appends (batch items) := by
  unfold batch
  repeat' first
    | source_history_join
    | source_history_join_use
    | source_history_reduce
    | (rx_append_head ite; apply Appends.ite)
    | (rx_append_head batchItem; exact batchItem_appends _ _ _)
    | (rx_append_head afterBatch; exact afterBatch_appends)
    | rx_append_step

theorem observe_appends : Appends observe :=
  Appends.bind idleTimers_appends (fun _ => Appends.lift _)

theorem afterXmit_appends : Appends afterXmit := by
  unfold afterXmit
  repeat' first
    | source_history_join
    | source_history_join_use
    | source_history_reduce
    | (rx_append_head ite; apply Appends.ite)
    | (rx_append_head runCryptWorkers; exact runCryptWorkers_appends)
    | (rx_append_head runSendWorkers; exact runSendWorkers_appends)
    | rx_append_step

theorem afterAdvance_appends : Appends afterAdvance := by
  unfold afterAdvance
  repeat' first
    | source_history_join
    | source_history_join_use
    | source_history_reduce
    | (rx_append_head ite; apply Appends.ite)
    | (rx_append_head runTimers
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runTimers_appends) _)
    | (rx_append_head runTimersPlaceholder
       exact (pinned_const _private.Leanux.Proofs.WG.Queues.RxWaitAppends.«0».Leanux.Proofs.WG.Queues.RxHistory.runTimersPlaceholder_appends) _)
    | rx_append_step

theorem socketCallOn_appends (fd : Nat) {body : Obs Int} (hb : Appends body) :
    Appends (socketCallOn fd body) := by
  unfold socketCallOn
  repeat' first | with_reducible exact hb | rx_append_step

theorem syscallDispatch_appends (call : Syscall) : Appends (syscallDispatch call) := by
  cases call <;> unfold syscallDispatch
  all_goals repeat' first
    | (rx_append_head socketCallOn; apply socketCallOn_appends)
    | (rx_append_head inject; exact inject_appends _ _ _ _ _ _)
    | (rx_append_head flood; exact flood_appends _ _ _ _)
    | (rx_append_head batch; exact batch_appends _)
    | (rx_append_head observe; exact observe_appends)
    | rx_append_step

end Leanux.Proofs.WG.Queues.RxHistory
