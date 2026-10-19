import Leanux.Proofs.WG.TransmitSecurity.DriverEffectsNeutral
import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveTrafficFrames

/-! The common driver's actual staging source preserves the allocation-indexed
timestamp archive, including no-key, nonce-limit and queue refusal paths. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity

abbrev Preserves (action : WGPrefix TimestampReceipt α) :=
  StatePrefixPreserves (fun h w _ => StateInv h w) History action

theorem lift (action : WG.M α)
    (preserved : ∀ h, Framing.Preserves (StateInv h) action) : Preserves (liftWGPrefix action) :=
  StatePrefixEnsures.lift _ (fun _ _ _ hi => hi.1)
    (fun h w a result v b hi run => (hoare_iff_run_ambient _ _ _).mp (preserved h) w a result v b hi run)

theorem selection (pid : PeerId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (Responder.selectionPrefix pid) := by
  unfold Responder.selectionPrefix
  apply hoare_bind _ _ (read_saved pid history)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient (AmbientM.branch .stagedEmpty p.staged.isEmpty) _)
  intro empty
  cases empty with
  | true => exact hoare_consequence (preserves_pure none) (fun _ hi => hi.1) (fun _ _ hi => hi)
  | false =>
    apply hoare_bind _ _ (write_saved pid p (fun current => {current with staged := []})
      (fun _ => ⟨rfl,rfl⟩) history)
    intro _
    exact preserves_bind (key_get p.keypairCurrent history)
      (fun kp => preserves_pure (some (p,kp)))

theorem ambient (a : AmbientM α) : Preserves (liftWGPrefix (monadLift a)) :=
  lift _ (fun confirmed => hoare_liftAmbient a (StateInv confirmed))

theorem same_world {a : WG.M α} (frame : SameView id a) : Preserves (liftWGPrefix a) :=
  lift _ (fun confirmed => frame.wp (StateInv confirmed))

theorem pure (x : α) : Preserves (pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi.1) (fun _ _ _ hi => hi)

theorem loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix TimestampReceipt (ForInStep β))
    (hg : ∀ x b, Preserves (g x b)) : Preserves (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => StateInv h w) History
    (fun _ _ _ _ hi => hi.1) hg

/-- The exact common staging path retains the timestamp archive across all
nonce allocation and packet queue decisions, including internally stopped runs. -/
theorem staging (pid : PeerId) : Preserves (Driver.stagingObserved TimestampDriver.hooks pid) := by
  change StatePrefixPreserves (fun h w _ => StateInv h w) History _
  unfold Driver.stagingObserved
  simp only [Driver.restore_noKey_lift TimestampDriver.hooks rfl rfl rfl]
  dsimp only [TimestampDriver.hooks]
  apply StatePrefixEnsures.bind (lift _ (selection pid))
  intro selected
  cases selected with
  | none => exact pure ()
  | some pair =>
    rcases pair with ⟨p,kp⟩
    have hout (invalid : Bool) := lift _ (fun confirmed => out_no_key pid p.staged kp invalid confirmed)
    apply StatePrefixEnsures.bind (ambient _)
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact ambient _
      | some id =>
        apply StatePrefixEnsures.bind (lift _ (fun confirmed => read_key id confirmed))
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
                 exact lift _ (fun confirmed => indexOwner_peerDeref_preserves _ (StateInv confirmed)))
              | (nonce_source_head peerGet; exact lift _ (peer_get _))
              | (nonce_source_head List.mapM; exact lift _ (allocate_packets _))
              | (nonce_source_head createData; exact lift _ (create _ _))
              | (nonce_source_head stagedOutNokey; exact hout true)
              | (nonce_source_head Pure.pure; exact pure _)
              | (nonce_source_head ForIn.forIn
                 apply loop
                 intro x b
                 change StatePrefixPreserves (fun h w _ => StateInv h w) History _)
              | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
              | split
              | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
