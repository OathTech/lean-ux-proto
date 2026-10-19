import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConsumeLeafPointEndpoint

/-! Both original unreference modes retain decrement, unhash and key erasure cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal


noncomputable def keyReleaseShape (kid : Option KeypairId) (unreferenceNow : Bool) :
    Shape (wg (keypairPut kid unreferenceNow)) := by
  apply Shape.marked (.keyRelease kid unreferenceNow)
  unfold keypairPut refcountDecAndTest
  repeat' first
    | (consume_leaf_wg_head IndexOwner.peerDeref; exact .native (.base (.dereference _)))
    | (consume_leaf_wg_head modifyDev; exact .native (.base (.eraseKey _)))
    | (consume_leaf_wg_head liftM; exact .native (.base (.unhash _)))
    | consume_leaf_shape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Consume.Leaf
