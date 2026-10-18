import Leanux.Proofs.WG.RetirementSecurity.RxFinishHolders
import Leanux.Proofs.WG.RetirementSecurity.OwnershipCompletionFrames

/-! The native index scan acquires a peer reference and stores its owner
word back. Neither operation changes the physical key-reference ledger;
the separate keypairGet in receive admission is the key acquisition. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem peerGetMaybe_ownership (pid : Option PeerId) :
    SameView ownershipPointView (peerGetMaybeZero pid) := by
  intro initial
  change Preserves (fun w => ownershipPointView w = initial) _
  unfold peerGetMaybeZero refcountIncNotZero
  simp only [requireNotPending,branch,branchCmp,unsupported,invariant]
  repeat' ownership_source_step initial

theorem ownerStore_holders (owner : IndexOwner) (word : Option PeerId)
    (temporary : Credits.Ledger) : Preserves (HolderAccount temporary) (owner.setPeerWord word) := by
  cases owner with
  | handshake pid =>
    exact ownership_preserves _ (by
      apply (updatePeer_ownership pid (fun p => {p with handshakeEntryPeer := word}))
      intro p
      rfl) temporary
  | keypair id =>
    exact key_update_holders id (fun k => {k with peer := word}) (fun _ => rfl)
      (fun _ => rfl) temporary

theorem acquireOwner_holders (owner : IndexOwner) (temporary : Credits.Ledger) :
    Preserves (HolderAccount temporary) (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  apply preserves_bind (indexOwner_peerWord_preserves owner _)
  intro word
  apply preserves_bind (by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b account run
    exact account.points ((ProjectedAction.iff_run_ambient _ _ _).mp
      (peerGetMaybe_ownership word) w a result v b run))
  intro result
  apply preserves_bind (ownerStore_holders owner result temporary)
  intro _
  exact preserves_pure _

private theorem indexLookup_preserves (kinds : List IndexKind) (index : Nat)
    (P : WGWorld → Prop) (hi : Preserves P (liftIndex (indexBucket index)))
    (acquire : ∀ owner, Preserves P (Affiliation.acquireOwner owner)) :
    Preserves P (indexLookup kinds index) := by
  have hb (decision : Decision) (value : Bool) :
      Preserves P (branch decision value : WG.M Bool) :=
    hoare_liftAmbient (AmbientM.branch decision value) P
  have stop {α : Type} (why : String) : Preserves P (invariant why : WG.M α) :=
    hoare_liftAmbient (AmbientM.invariant why) P
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  repeat' first
    | unfold Preserves
    | material_join
    | material_join_use
    | (index_material_head branch; exact hb _ _)
    | (index_material_head invariant; exact stop _)
    | (index_material_head liftIndex; exact hi)
    | (index_material_head Affiliation.acquireOwner; exact acquire _)
    | (index_material_head Pure.pure; exact preserves_pure _)
    | (index_material_head Bind.bind; apply preserves_bind)
    | (index_material_head ForIn.forIn; apply list_view_spec id P)
    | material_intro
    | material_reduce
    | material_match
    | (index_material_head ite; split)

theorem indexLookup_holders (kinds : List IndexKind) (index : Nat)
    (temporary : Credits.Ledger) : Preserves (HolderAccount temporary) (indexLookup kinds index) := by
  apply indexLookup_preserves kinds index (HolderAccount temporary) _
    (fun owner => acquireOwner_holders owner temporary)
  apply hoare_liftIndex
  intro w d table account device
  apply account.store
  simp [holderStore,Origins.view,peersAt,packetKeyWords,device]

end Leanux.Proofs.WG.RetirementSecurity
