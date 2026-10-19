import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceHistory
import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral

/-! Actual shared staging preserves positive resident peer counts through
current selection, nonce-limit restoration, allocation and queue failure. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
variable {E : Type} [EntryFormat E]
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

theorem selection (pid : PeerId) :
    Framing.Preserves Inv (Responder.selectionPrefix pid) := by
  unfold Responder.selectionPrefix
  apply hoare_bind _ _ (read_saved pid)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) _)
  intro empty
  cases empty with
  | true => exact hoare_consequence (preserves_pure none) (fun _ hi => hi.1) (fun _ _ hi => hi)
  | false =>
    apply hoare_bind _ _ (write_saved pid p (fun current => {current with staged := []})
      (fun _ => rfl))
    intro _
    exact preserves_bind (key_get p.keypairCurrent)
      (fun kp => preserves_pure (some (p,kp)))

/-- The exact common staging path retains the positive-reference carrier across all
nonce allocation and packet queue decisions, including internally stopped runs. -/
theorem staging (pid : PeerId) : Observed (E := E) (Driver.stagingObserved EntrySource.hooks (E := E) pid) := by
  change StatePrefixPreserves (fun h w _ => StateInv (E := E) h w) (Safe (E := E)) _
  unfold Driver.stagingObserved
  simp only [Driver.noKey_lift EntrySource.hooks (E := E) rfl]
  dsimp only [EntrySource.hooks]
  apply StatePrefixEnsures.bind (lift _ (selection pid))
  intro selected
  cases selected with
  | none => exact pure ()
  | some pair =>
    rcases pair with ⟨p,kp⟩
    have hout (invalid : Bool) := lift (E := E) _ (out_no_key pid p.staged kp invalid)
    apply StatePrefixEnsures.bind (ambient _)
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact ambient _
      | some id =>
        apply StatePrefixEnsures.bind (lift _ (read_key id))
        intro k
        apply StatePrefixEnsures.bind (ambient _)
        intro invalid
        split
        · exact hout false
        · apply StatePrefixEnsures.bind (same_world (branchExpired_sameWGWorld _ _ _ _))
          intro expired
          split
          · exact hout true
          · try dsimp only
            repeat' first
              | (nonce_source_head Nonce.reserveNative; exact lift _ (reserve _))
              | (first | nonce_source_head branch | nonce_source_head branchCmp
                 exact ambient _)
              | (nonce_source_head ipTunnelEcnEncap; exact same_world (ipTunnelEcnEncap_sameWGWorld _))
              | (nonce_source_head IndexOwner.peerDeref
                 exact lift _ (indexOwner_peerDeref_preserves _ Inv))
              | (nonce_source_head peerGet; exact lift _ (peer_get _))
              | (nonce_source_head List.mapM; exact lift _ (allocate_packets _))
              | (nonce_source_head createData; exact lift _ (create _ _))
              | (nonce_source_head stagedOutNokey; exact hout true)
              | (nonce_source_head Pure.pure; exact pure _)
              | (nonce_source_head ForIn.forIn
                 apply loop
                 intro x b
                 change StatePrefixPreserves (fun h w _ => StateInv (E := E) h w) (Safe (E := E)) _)
              | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
              | split
              | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
