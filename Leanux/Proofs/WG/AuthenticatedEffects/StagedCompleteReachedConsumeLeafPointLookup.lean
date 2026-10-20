import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointKey

/-! Routing lookup retains its actual acquired peer and original retry refusal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal


noncomputable def lookupNodeShape (root : Option NodeId) (bits key : Nat) :
    Shape (wg (lookup root bits key)) := by
  apply Shape.marked (.lookupNode root bits key)
  unfold lookup
  repeat' first
    | (consume_leaf_wg_head swapEndian; exact .native (.metadata _ (PeerMetadata.endianShape _)))
    | (consume_leaf_wg_head liftM; exact .native (.metadata _ (Routing.aipShape _)))
    | (consume_leaf_wg_head peerGetMaybeZero; exact .native (.acquire _))
    | consume_leaf_shape

noncomputable def lookupShape (protocol : Nat) (bytes : List UInt8) :
    Shape (wg (lookupSrc protocol bytes)) := by
  apply Shape.marked (.lookup protocol bytes)
  unfold lookupSrc
  repeat' first
    | (consume_leaf_wg_head lookup; exact lookupNodeShape _ _ _)
    | consume_leaf_shape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
