import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverTxFrames

/-! Actual staged-send source transport for the common driver responder
projection, including no-key, age, nonce-limit and queue-refusal paths. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

theorem ambient (a : AmbientM α) : Preserves (liftWGPrefix (monadLift a)) :=
  lift _ (fun confirmed => hoare_liftAmbient a (Carrier confirmed))

theorem same_world {a : WG.M α} (frame : SameView id a) : Preserves (liftWGPrefix a) :=
  lift _ (fun confirmed => frame.wp (Carrier confirmed))

theorem pure (x : α) : Preserves (pure x) :=
  StatePrefixEnsures.pure x (fun _ _ _ hi => hi.2) (fun _ _ _ hi => hi)

theorem loop {α β : Type} (xs : List α) (b : β)
    (g : α → β → WGPrefix Event (ForInStep β))
    (hg : ∀ x b, Preserves (g x b)) : Preserves (forIn xs b g) :=
  StatePrefixEnsures.forInInvariant xs b g (fun _ h w _ => Inv h w) Safe
    (fun _ _ _ _ hi => hi.2) hg

/-- Every selection receipt in the actual staging implementation is checked
against entry authorization; reservations and allocations retain the same
carrier through all normal paths, and later Stops retain prior checks. -/
theorem staging (pid : PeerId) : Preserves (Driver.stagingObserved hooks pid) := by
  change StatePrefixPreserves (fun h w _ => Inv h w) Safe _
  unfold Driver.stagingObserved
  dsimp only [hooks]
  apply StatePrefixEnsures.bind (selection_preserves pid)
  intro selected
  cases selected with
  | none => exact pure ()
  | some pair =>
    rcases pair with ⟨p,kp⟩
    have hout (invalid : Bool) := lift _ (fun confirmed => carrier_out pid p.staged kp invalid confirmed)
    apply StatePrefixEnsures.bind (ambient _)
    intro missing
    split
    · exact hout false
    · cases kp with
      | none => exact ambient _
      | some id =>
        apply StatePrefixEnsures.bind (lift _ (fun confirmed => carrier_key_read id confirmed))
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
              | (nonce_source_head Nonce.reserveNative; exact lift _ (carrier_reserve _))
              | (first | nonce_source_head branch | nonce_source_head branchCmp
                 exact ambient _)
              | (nonce_source_head ipTunnelEcnEncap; exact same_world (ipTunnelEcnEncap_sameWGWorld _))
              | (nonce_source_head IndexOwner.peerDeref
                 exact lift _ (fun confirmed => indexOwner_peerDeref_preserves _ (Carrier confirmed)))
              | (nonce_source_head peerGet; exact lift _ (carrier_peer_get _))
              | (nonce_source_head List.mapM; exact lift _ (carrier_allocate _))
              | (nonce_source_head createData; exact lift _ (carrier_create _ _))
              | (nonce_source_head stagedOutNokey; exact hout true)
              | (nonce_source_head Pure.pure; exact pure _)
              | (nonce_source_head ForIn.forIn
                 apply loop
                 intro x b
                 change StatePrefixPreserves (fun h w _ => Inv h w) Safe _)
              | (nonce_source_head Bind.bind; apply StatePrefixEnsures.bind)
              | split
              | (with_reducible intro x; try dsimp only)

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
