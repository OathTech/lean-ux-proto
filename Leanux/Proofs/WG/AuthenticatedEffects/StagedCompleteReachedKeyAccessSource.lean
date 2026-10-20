import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedPreparePointCanonicalFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedStagingPrimitiveFrames

/-! Fixed lifetime-observed key repayment. The shared access-point language
keeps native getters/setters and their following receipts separate. Erasure
retains the original release event, even before that event is emitted. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeyAccess
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity CausalJournal Prepare.Points
set_option maxHeartbeats 600000

theorem erase_factor (id stamp : Nat) :
    eraseKeypairPrefix id stamp =
      receiptWGObserved (liftWGPrefix (modifyDev fun d=>{d with keypairs:=d.keypairs.erase id}))
        (fun _=>LifetimeEvent.keypair (.release id stamp)) := by
  funext w a h
  rfl

noncomputable def eraseShape (id stamp : Nat) : Shape (eraseKeypairPrefix id stamp) := by
  rw [erase_factor]
  exact .receipt (.quiet _ (StagingPrimitive.KeyAtom.frame (.erase id))) _

noncomputable def removeShape (id : KeypairId) : Shape (removeKeypairEntryPrefix id) := by
  unfold removeKeypairEntryPrefix
  exact .bind (peerDeref id) (fun _=>.metadata _ (.access (PeerMetadata.indexShape (indexRemove (.keypair id)))))

noncomputable def canonical (kid : Option KeypairId) (now : Bool) :
    Shape (keypairPutPrefix kid now) := by
  unfold keypairPutPrefix refcountDecAndTest
  repeat' first
    | (prepare_shape_head removeKeypairEntryPrefix; exact removeShape _)
    | (prepare_shape_head eraseKeypairPrefix; exact eraseShape _ _)
    | prepare_shape_step

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.KeyAccess
