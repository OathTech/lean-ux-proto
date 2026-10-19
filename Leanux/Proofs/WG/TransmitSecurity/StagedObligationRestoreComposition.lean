import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreCompositionCuts

/-! The actual reservation observer and native checked continuation retain the
fixed selected tickets. A no-key branch transfers that ledger at its original
restore receipt, while the caller supplies the later queue/submission contracts.
These normal-return contracts use True as the history predicate; they do not
establish the selected/allocated ownership frontier of a stopped execution. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreComposition
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects.CausalJournal HandshakeSecurity.StagedConservation

private def Done (Post : List Event → WGWorld → Ambient → Prop)
    (acc : Option Unit × List DataPacket) (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  Post h w a ∧ acc.1.isSome = true

private def Continuing (ledger : Ledger) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (acc : Option Unit × List DataPacket) (h : List Event) (w : WGWorld) (a : Ambient) : Prop :=
  Held ledger generation pid peer position h w a ∧ acc.1 = none

/-- Every actual reservation in the original nonce loop preserves the same
ledger and selected packet order. The no-key and submission contracts are
local callback obligations, not an assumed initialized conservation result. -/
theorem checked_held (ledger : Ledger) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (keypair : Option KeypairId) (Post : List Event → WGWorld → Ambient → Prop)
    (noKey : Option KeypairId → Bool → WGPrefix Event Unit)
    (submit : KeypairId → List DataPacket → WGPrefix Event Unit)
    (rejected : ∀ kp invalid, StatePrefixEnsures (Held ledger generation pid peer position) (fun _ => True)
      (noKey kp invalid) (fun _ => Post))
    (submitted : ∀ kid packets, StatePrefixEnsures (Held ledger generation pid peer position) (fun _ => True)
      (submit kid packets) (fun _ => Post)) :
    StatePrefixEnsures (Held ledger generation pid peer position) (fun _ => True)
      (RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid)) noKey submit pid peer keypair)
      (fun _ => Post) := by
  unfold RestoreEntry.checkedWith
  apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedNoKeypair keypair.isNone))
  intro missing
  split
  · exact rejected keypair false
  · cases keypair with
    | none =>
      apply StatePrefixEnsures.lift _ (fun _ _ _ _ => True.intro)
      intro h w a value v b before run
      cases run
    | some id =>
      apply StatePrefixEnsures.bind (held_read_key id)
      intro key
      apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedKeyInvalid !key.sending.isValid))
      intro invalid
      split
      · exact rejected (some id) false
      · apply StatePrefixEnsures.bind (held_world _ (branchExpired_sameWGWorld _ _ _ _))
        intro expired
        split
        · exact rejected (some id) true
        · apply StatePrefixEnsures.bind
          · apply StatePrefixEnsures.consequence
              (P := Continuing ledger generation pid peer position (none,[]))
            · apply forIn_processed peer.staged [] (none,[]) _
                (fun _ => Continuing ledger generation pid peer position) (Done Post) (fun _ => True)
                (fun _ _ _ _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro)
              intro packet seen acc
              apply StatePrefixEnsures.consequence (P := Held ledger generation pid peer position)
                (Q := fun result => match result with
                  | .done next => Done Post next
                  | .yield next => Continuing ledger generation pid peer position next)
              · apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedNonceIterate true))
                intro _
                apply StatePrefixEnsures.bind (held_world _ (ipTunnelEcnEncap_sameWGWorld packet))
                intro ds
                apply StatePrefixEnsures.bind (reservation_held id)
                intro nonce
                apply StatePrefixEnsures.bind (held_ambient (AmbientM.branchCmp .stagedNonceRejected
                  (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES))
                intro over
                cases over with
                | true =>
                  apply StatePrefixEnsures.bind (rejected (some id) true)
                  intro out
                  exact StatePrefixEnsures.pure _ (fun _ _ _ _ => True.intro)
                    (fun _ _ _ before => ⟨before,rfl⟩)
                | false =>
                  exact StatePrefixEnsures.pure _ (fun _ _ _ _ => True.intro)
                    (fun _ _ _ before => ⟨before,rfl⟩)
              · exact fun _ _ _ before => before.1
              · intro result h w a after
                cases result <;> exact after
            · exact fun _ _ _ before => ⟨before,rfl⟩
            · exact fun _ _ _ _ after => after
          · intro acc
            obtain ⟨done,packets⟩ := acc
            cases done with
            | some out =>
              apply StatePrefixEnsures.pure _ (fun _ _ _ _ => True.intro)
              intro h w a before
              rcases before with done | continuing
              · exact done.1
              · cases continuing.2
            | none =>
              apply StatePrefixEnsures.consequence (P := Held ledger generation pid peer position)
                (Q := fun _ => Post)
              · exact StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedNonceIterate false))
                  (fun _ => submitted id packets)
              · intro h w a before
                rcases before with done | continuing
                · simp [Done] at done
                · exact continuing.1
              · exact fun _ _ _ _ after => after

/-- This local source join starts immediately after the actual take: borrowing,
the original checked continuation and the actual restore observer keep the same
selected tickets. Queueing after restoration and successful TX submission remain
explicit callbacks because they may perform further ledger transfers. -/
theorem borrow_checked_restore (record : Restore.Receipt → Event) (ledger : Ledger)
    (valid : Valid births ledger) (generation : Nat) (pid : PeerId) (peer : Peer) (position : Nat)
    (o : AuthenticatedEffects.TimerEffects.Ops (WGPrefix Event))
    (native : ∀ {α} (action : WG.M α), o.step action = liftWGPrefix action)
    (queue : PeerId → Bool → WGPrefix Event Unit)
    (submit : KeypairId → List DataPacket → WGPrefix Event Unit)
    (Post : List Event → WGWorld → Ambient → Prop)
    (queued : StatePrefixEnsures (Restored births ledger generation pid peer position) (fun _ => True)
      (queue pid false) (fun _ => Post))
    (submitted : ∀ kid packets, StatePrefixEnsures (Held ledger generation pid peer position) (fun _ => True)
      (submit kid packets) (fun _ => Post)) :
    StatePrefixEnsures (Held ledger generation pid peer position) (fun _ => True) (do
      let selected ← liftWGPrefix (Take.borrow (some peer))
      match selected with
      | none => pure ()
      | some (chosen,keypair) =>
        RestoreEntry.checkedWith liftWGPrefix (fun kid => state (Journal.reserve kid))
          (fun kp invalid => Restore.noKeyWith o (Restore.observed record) queue pid chosen.staged kp invalid)
          submit pid chosen keypair) (fun _ => Post) := by
  apply StatePrefixEnsures.bind (borrow_held ledger generation pid peer position)
  intro selected
  cases selected with
  | none =>
    intro w a h before
    obtain ⟨_,impossible,_⟩ := before
    cases impossible
  | some chosen =>
    obtain ⟨selected,keypair⟩ := chosen
    intro w a h before
    obtain ⟨borrowed,same,held⟩ := before
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj same)
    exact (checked_held ledger generation pid selected position keypair Post _ _
      (fun kp invalid => no_key_restores record ledger valid generation pid selected position kp invalid
        o native queue Post queued) submitted) w a h held

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreComposition
