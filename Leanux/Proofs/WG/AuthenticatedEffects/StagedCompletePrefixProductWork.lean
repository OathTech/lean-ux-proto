import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProductWorkFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixSendWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixClearWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixProductSource

/-! Scheduled send and clear preserve all logical prefixes together with
both directions of packet accounting and native allocation. The clear callback retains its actual peer-release
settlement; only the scheduler's selector and queue bookkeeping are passive. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Queues.RxCredits

private theorem send_state (pid : PeerId) : StateChecked (CausalJournal.flushedSend pid) :=
  pair (Send.flushed CompleteProduct.Safe CompleteProduct.account_safe pid)
    (CompleteProduct.pair (CompleteSend.flushed CompleteProduct.Safe CompleteProduct.account_safe pid)
      (CompleteProduct.WorkNative.send_erases pid) (CompleteProduct.WorkNative.send_allocated pid))

private theorem clear_state (pid : PeerId) :
    StateChecked (NestedPeerRelease.clearWith (Driver.nestedOps hooks) pid) :=
  pair (Clear.clear CompleteProduct.Safe CompleteProduct.account_safe pid)
    (CompleteProduct.pair (CompleteClear.clear CompleteProduct.Safe CompleteProduct.account_safe pid)
      (CompleteProduct.WorkNative.clear_erases pid) (CompleteProduct.WorkNative.clear_allocated pid))

theorem scheduled_send : Checked (Driver.sendWorkerObserved hooks) := by
  change Checked (HandshakeSecurity.SendExchange.oneWith liftPrefix
    (fun pid => liftWGObserver (CausalJournal.flushedSend pid)))
  exact bind_checked (native _ WorkFrames.send_select) (fun pid => state (send_state pid))

theorem scheduled_clear : Checked (Driver.clearWorkerObserved hooks) := by
  unfold Driver.clearWorkerObserved NestedPeerRelease.oneClearWith
  repeat' first
    | (prefix_product_head runWorkerPrefix
       apply runWorkerPrefix_preserves carrier_safe stable
       exact state (clear_state _))
    | (prefix_product_native liftWG
       first
       | exact product_store _ (liftWG_sameProductStore _ getDev_sameWGStore)
       | exact native _ (WorkFrames.clear_dequeue _))
    | (prefix_product_native invariant; exact ambient _)
    | (prefix_product_native peekUnit; exact ambient _)
    | (prefix_product_native resolveUnit; exact ambient _)
    | prefix_product_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Product
