import Leanux.Proofs.WG.TransmitSecurity.StagedCompletionFrames
import Leanux.Proofs.WG.TransmitSecurity.StagedTimerCallbackFrames

/-! Native completion frames retain staged origins. These contracts
allow peer repayment to remove a queue and do not assert disposal coverage. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

theorem complete (pid : PeerId) (items : List SkbId) :
    Preserves (Inv h) (createDataDone pid items) := by
  unfold createDataDone WG.andM
  repeat' first
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv h)
       intro x b
       change Preserves (Inv h) _)
    | (rx_retention_head getTxSkb; exact skb _)
    | (rx_retention_head timersTraversal; exact traversal _)
    | (rx_retention_head sendSkbToPeer; exact send_skb _ _ _)
    | (rx_retention_head timersDataSent; exact data_sent _)
    | (rx_retention_head keepKeyFresh; exact fresh_send _)
    | staged_origin_native

private theorem body (pid : PeerId) (first : Option (List SkbId)) :
    Preserves (Inv h) (TxDisposition.bodySource pid first) := by
  unfold TxDisposition.bodySource WG.andM
  repeat' first
    | exact drop_completion pid
    | (rx_retention_head createDataDone; exact complete _ _)
    | (rx_retention_head TxDisposition.disposeSource; exact dispose_completion _ _ _)
    | (rx_retention_head getTxSkb; exact skb _)
    | staged_origin_native

theorem transmit (pid : PeerId) : Preserves (Inv h) (txStep pid) := by
  rw [← TxDisposition.stepSource_eq]
  unfold TxDisposition.stepSource
  repeat' first
    | (rx_retention_head TxDisposition.bodySource; exact body _ _)
    | (rx_retention_head PrevQueue.peek; exact store (prevQueuePeek_sameWGStore _))
    | staged_origin_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
