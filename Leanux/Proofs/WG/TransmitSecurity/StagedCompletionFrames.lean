import Leanux.Proofs.WG.TransmitSecurity.StagedWorkerFrames

/-! Exact native TX queue removal and reference disposal preserve origins of
surviving staged packets. These frames do not assert disposition coverage. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000

theorem drop_completion (pid : PeerId) : Preserves (Inv h)
    (do setPeer pid {(← getPeer pid) with txQueue := (← getPeer pid).txQueue.dropPeeked}) := by
  rw [getPeer_twice]
  repeat' staged_origin_native

theorem dispose_completion (pid : PeerId) (items : List SkbId) (key : KeypairId) :
    Preserves (Inv h) (TxDisposition.disposeSource pid items key) := by
  unfold TxDisposition.disposeSource
  repeat' first
    | (rx_retention_head freeTxSkb; exact skb _)
    | (rx_retention_head keypairPut; exact key_put _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv h)
       intro id state
       change Preserves (Inv h) _)
    | staged_origin_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
