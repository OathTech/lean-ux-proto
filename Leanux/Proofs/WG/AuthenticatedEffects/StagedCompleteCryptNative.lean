import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteProductNapiFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteEncryptSource
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteDecryptSource
import Leanux.Proofs.WG.Queues.RxWorkerHistory

/-! Exact native allocation counterparts for ring, encryption and preparation.
The state companion is transported on the same run as the paired journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.CryptNative
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity CausalJournal StackOwnership RxWorkers
set_option maxHeartbeats 600000

theorem encrypt_step_erases (item : Option (List SkbId)) :
    ErasesPrefix (encryptStepTail item) (encryptStepTailSource item) := by
  unfold encryptStepTail encryptStepTailSource
  repeat' first
    | exact encryptPacketPrefix_erases (fun _ => erasesPrefix_lift _) _ _
    | exact liftWGObserver_erases (getTxSkbPrefix_erases _)
    | exact liftWGObserver_erases (setTxSkbPrefix_erases _ _)
    | exact liftWGObserver_erases (enqueuePerPeerTxPrefix_erases _ _)
    | exact erasesPrefix_lift _
    | exact erasesPrefix_pure _
    | apply erasesPrefix_forIn
    | apply erasesPrefix_bind
    | apply erasesPrefix_ite
    | split
    | (with_reducible intro x; try dsimp only)

theorem encrypt_step_allocation (item : Option (List SkbId)) :
    PrefixPreserves (fun h w => AllocationInv h w.wg) LifetimeEvent.Safe (encryptStepTail item) := by
  let c := ProductAmbientContracts.ofNative allocationAmbient
  let t := ProductTxContracts.ofNative allocationTx
  unfold encryptStepTail
  apply PrefixPreserves.bind (ProductAmbientContracts.drop (c.branch (fun _ => True) _ _))
  intro _
  cases item with
  | none => exact PrefixPreserves.pure c.safe _
  | some first =>
    dsimp only
    cases he : first.head? with
    | none => exact ProductAmbientContracts.drop (c.invariant (fun _ => True) _)
    | some headId =>
      repeat' first
        | with_reducible exact encryptPacketPrefix_allocation _ _
        | with_reducible exact enqueuePerPeerTxPrefix_preserves_product c t _ _
        | with_reducible exact ProductAmbientContracts.drop (t.get (fun _ => True) _)
        | with_reducible exact ProductAmbientContracts.drop (t.set (fun _ => True) _ _)
        | with_reducible exact ProductAmbientContracts.drop (c.branch (fun _ => True) _ _)
        | with_reducible exact PrefixPreserves.pure c.safe _
        | with_reducible apply PrefixPreserves.forIn _ _ _ c.safe
        | with_reducible apply PrefixPreserves.bind
        | with_reducible apply PrefixPreserves.ite
        | (with_reducible split)
        | (with_reducible intro x; try dsimp only)

theorem poll_erases : ErasesPrefix hooks.poll (liftWG TxRing.pollSource) := by
  apply EncryptionHistory.projected_erases hooks_projects.poll
  apply EncryptionHistory.projected_erases Journal.hooks_projects.poll
  exact erasesPrefix_lift _

theorem prepare_erases : ErasesPrefix hooks.prepare (liftWG RxWorkers.prepareSource) := by
  apply EncryptionHistory.projected_erases hooks_projects.prepare
  apply EncryptionHistory.projected_erases Journal.hooks_projects.prepare
  exact erasesPrefix_lift _

theorem poll : Preserves (fun w : World => Allocated w.wg) (liftWG TxRing.pollSource) :=
  native_allocated_product (liftWGObserver_erases (erasesStatePrefix_lift _))
    (pinned_const _private.Leanux.Proofs.WG.Queues.RxWorkerHistory.«0».Leanux.Proofs.WG.Queues.RxHistory.encryptPoll_allocation)

theorem prepare : Preserves (fun w : World => Allocated w.wg) (liftWG RxWorkers.prepareSource) :=
  PublicationPoll.native_product Allocated _
    (AllocatedFrames.observed RxWorkers.prepare_erases RxWorkers.prepare_preserves)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteProduct.CryptNative
