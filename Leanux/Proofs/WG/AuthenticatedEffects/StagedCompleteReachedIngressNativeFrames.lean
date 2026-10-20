import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIngressSource

/-! RX allocation and erasure preserve the existing TX account through
their actual packet-bound contracts. They are not equality frames of the
shared packet store or independent births in the TX ledger. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal Driver NestedPeerRelease

theorem NativeKind.checked (kind : NativeKind) : CompleteProduct.Checked kind.action := by
  cases kind with
  | quiet body frame allocated=>
      exact CompleteProduct.state (CompleteConfigurationReady.passive CompleteProduct.Safe
        CompleteProduct.account_safe body frame allocated)
  | allocate packet=>
      exact CompleteProduct.state (CompleteProduct.pair
        (CompleteIngress.new_rx CompleteProduct.Safe CompleteProduct.account_safe packet)
        (erasesStatePrefix_lift _)
        (AllocatedFrames.observed (PacketAllocation.erases (.rx packet)) (PacketAllocation.preserves (.rx packet))))
  | free skb=>
      exact CompleteProduct.state (CompleteProduct.pair
        (CompletePollNative.free_rx CompleteProduct.Safe CompleteProduct.account_safe skb)
        (erasesStatePrefix_lift _)
        (AllocatedFrames.observed (freeRxSkbPrefix_erases skb) (freeRxSkbPrefix_allocation skb)))

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Ingress
