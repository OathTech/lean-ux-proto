import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceFrames

/-! Reference positivity through original key and owner operations. Index
lookup preserves the invariant even though its arbitrary-state zero branch
can clear an owner word; initialized exclusion is proved separately. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins
open ConfiguredReceive

macro "peer_reference_step" : tactic => `(tactic| first
  | (receive_update_head Bind.bind
     apply update_peer_bind
     · intro p positive; exact positive
     intro x)
  | (receive_update_head setPeer; apply update_peer; intro p positive; exact positive)
  | (rx_retention_head getPeer; exact read_peer _)
  | (rx_retention_head getKeypair; exact read_key _)
  | (rx_retention_head setKeypair; exact write_key _ _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get Inv) (fun _ h => h) (fun _ _ h => h.2))
  | (rx_retention_head modify; apply modify_world; intro w; rfl)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head modifyDev; apply modify_device; intro d; rfl)
  | (rx_retention_head liftIndex; exact index _)
  | (rx_retention_head liftSkb; exact skb _)
  | (rx_retention_head peerPut; exact peer_put _)
  | (rx_retention_head peerGetMaybeZero; exact maybe_peer _)
  | (rx_retention_head IndexOwner.peerWord; exact indexOwner_peerWord_preserves _ Inv)
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ Inv)
  | (allocation_release_lift_from IndexM; exact index _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (first | rx_retention_head throw | rx_retention_head MonadExceptOf.throw
     apply (hoare_iff_run_ambient _ _ _).mpr
     intro w a result v b hi run
     cases run)
  | rx_retention_step)

theorem key_get (kid : Option KeypairId) : Preserves Inv (keypairGet kid) := by
  unfold keypairGet
  simp (config := {zeta := false}) only [refcountIncNotZero,branch,branchCmp,unsupported,invariant]
  repeat' peer_reference_step

theorem key_put (kid : Option KeypairId) (now : Bool) : Preserves Inv (keypairPut kid now) := by
  unfold keypairPut
  simp (config := {zeta := false}) only [refcountDecAndTest,branch,branchCmp,unsupported,invariant]
  repeat' peer_reference_step

theorem owner_write (owner : IndexOwner) (peer : Option PeerId) : Preserves Inv (owner.setPeerWord peer) := by
  cases owner with
  | handshake pid =>
    exact update_peer pid (fun p => {p with handshakeEntryPeer := peer}) (fun _ positive => positive)
  | keypair kid =>
    change Framing.Preserves Inv (getKeypair kid >>= _)
    apply preserves_bind (read_key kid)
    intro key
    exact write_key kid _

theorem acquire_owner (owner : IndexOwner) : Preserves Inv (Affiliation.acquireOwner owner) := by
  unfold Affiliation.acquireOwner
  repeat' first
    | (rx_retention_head IndexOwner.setPeerWord; exact owner_write _ _)
    | peer_reference_step

theorem lookup (kinds : List IndexKind) (number : Nat) : Preserves Inv (indexLookup kinds number) := by
  rw [← Affiliation.indexLookupSource_eq]
  unfold Affiliation.indexLookupSource
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head Affiliation.acquireOwner; exact acquire_owner _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id Inv
       intro x b
       change Framing.Preserves Inv _)
    | peer_reference_step

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
