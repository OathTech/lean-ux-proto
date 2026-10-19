import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreEntryFrames
import Leanux.Proofs.WG.TransmitSecurity.StagingProcessed

/-! Callback contracts for the original staging guards and nonce loop. Every
reached no-key callback receives the same empty peer allocation; its restore
callback receives that fact after the original invalidation/release prefix.
The history predicate also covers errors before either enclosing call returns. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreEntry
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes AuthenticatedEffects
open HandshakeSecurity.StagedConservation

private def Done (Post : List E → WGWorld → Ambient → Prop)
    (acc : Option Unit × List DataPacket) (h : List E) (w : WGWorld) (a : Ambient) : Prop :=
  Post h w a ∧ acc.1.isSome = true

private def Continuing (generation : Nat) (pid : PeerId) (allocation : Nat) (Safe : List E → Prop)
    (acc : Option Unit × List DataPacket) (h : List E) (w : WGWorld) (a : Ambient) : Prop :=
  Entry generation pid allocation Safe h w a ∧ acc.1 = none

/-- The callbacks are discharged at their actual source entries: no-key gets
the cleared original allocation even after multiple native nonce reservations.
Only the reservation observer's local entry contract is parameterized; all
key/age tests and intervening native operations are proved here. -/
theorem checked_entry (generation : Nat) (pid : PeerId) (peer : Peer)
    (keypair : Option KeypairId) (Safe : List E → Prop)
    (Post : List E → WGWorld → Ambient → Prop)
    (post_safe : ∀ h w a, Post h w a → Safe h)
    (reserve : KeypairId → WGPrefix E Nat)
    (noKey : Option KeypairId → Bool → WGPrefix E Unit)
    (submit : KeypairId → List DataPacket → WGPrefix E Unit)
    (reserved : ∀ kid, StatePrefixPreserves (Entry generation pid peer.internalId Safe) Safe (reserve kid))
    (rejected : ∀ kp invalid, StatePrefixEnsures (Entry generation pid peer.internalId Safe) Safe
      (noKey kp invalid) (fun _ => Post))
    (submitted : ∀ kid packets, StatePrefixEnsures (Entry generation pid peer.internalId Safe) Safe
      (submit kid packets) (fun _ => Post)) :
    StatePrefixEnsures (Entry generation pid peer.internalId Safe) Safe
      (checkedWith liftWGPrefix reserve noKey submit pid peer keypair) (fun _ => Post) := by
  unfold checkedWith
  apply StatePrefixEnsures.bind (entry_ambient (AmbientM.branch .stagedNoKeypair keypair.isNone))
  intro missing
  split
  · exact rejected keypair false
  · cases keypair with
    | none =>
      apply StatePrefixEnsures.lift _ (fun _ _ _ before => before.2)
      intro h w a value v b before run
      cases run
    | some id =>
      apply StatePrefixEnsures.bind (entry_read_key id)
      intro key
      apply StatePrefixEnsures.bind (entry_ambient (AmbientM.branch .stagedKeyInvalid !key.sending.isValid))
      intro invalid
      split
      · exact rejected (some id) false
      · apply StatePrefixEnsures.bind (entry_world _ (branchExpired_sameWGWorld _ _ _ _))
        intro expired
        split
        · exact rejected (some id) true
        · apply StatePrefixEnsures.bind
          · apply StatePrefixEnsures.consequence
              (P := Continuing generation pid peer.internalId Safe (none,[]))
            · apply forIn_processed peer.staged [] (none,[]) _
                (fun _ => Continuing generation pid peer.internalId Safe) (Done Post) Safe
                (fun _ _ _ _ _ before => before.1.2)
                (fun _ h w a before => post_safe h w a before.1)
              intro packet seen acc
              apply StatePrefixEnsures.consequence (P := Entry generation pid peer.internalId Safe)
                (Q := fun result => match result with
                  | .done next => Done Post next
                  | .yield next => Continuing generation pid peer.internalId Safe next)
              · apply StatePrefixEnsures.bind (entry_ambient (AmbientM.branch .stagedNonceIterate true))
                intro _
                apply StatePrefixEnsures.bind (entry_world _ (ipTunnelEcnEncap_sameWGWorld packet))
                intro ds
                apply StatePrefixEnsures.bind (reserved id)
                intro nonce
                apply StatePrefixEnsures.bind (entry_ambient (AmbientM.branchCmp .stagedNonceRejected
                  (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES))
                intro over
                cases over with
                | true =>
                  apply StatePrefixEnsures.bind (rejected (some id) true)
                  intro out
                  exact StatePrefixEnsures.pure _ post_safe (fun _ _ _ before => ⟨before,rfl⟩)
                | false =>
                  exact StatePrefixEnsures.pure _ (fun _ _ _ before => before.2)
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
              apply StatePrefixEnsures.pure _
                (fun h w a before => before.elim (fun h => post_safe _ _ _ h.1) (fun h => h.1.2))
              intro h w a before
              rcases before with done | entry
              · exact done.1
              · cases entry.2
            | none =>
              apply StatePrefixEnsures.consequence (P := Entry generation pid peer.internalId Safe)
                (Q := fun _ => Post)
              · exact StatePrefixEnsures.bind (entry_ambient (AmbientM.branch .stagedNonceIterate false))
                  (fun _ => submitted id packets)
              · intro h w a before
                rcases before with done | entry
                · simp [Done] at done
                · exact entry.1
              · exact fun _ _ _ _ after => after

/-- This is the concrete original prefix before the restore callback, including
optional sending invalidation and key repayment. Its source factor keeps the
callback before queueing the handshake request, so later Stops cannot require
assuming that request or the entire send completed. -/
theorem no_key_entry (generation : Nat) (pid : PeerId) (peer : Peer)
    (keypair : Option KeypairId) (invalid : Bool) (Safe : List E → Prop)
    (Middle Post : List E → WGWorld → Ambient → Prop)
    (o : TimerEffects.Ops (WGPrefix E))
    (native : ∀ {α} (action : WG.M α), o.step action = liftWGPrefix action)
    (restore : PeerId → List Packet → WGPrefix E Unit)
    (queue : PeerId → Bool → WGPrefix E Unit)
    (restored : StatePrefixEnsures (Entry generation pid peer.internalId Safe) Safe
      (restore pid peer.staged) (fun _ => Middle))
    (queued : StatePrefixEnsures Middle Safe (queue pid false) (fun _ => Post)) :
    StatePrefixEnsures (Entry generation pid peer.internalId Safe) Safe
      (Restore.noKeyWith o restore queue pid peer.staged keypair invalid) (fun _ => Post) := by
  rw [no_key_factor]
  have step : @o.step = (fun {α} (action : WG.M α) => (liftWGPrefix action : WGPrefix E α)) := by
    funext α action
    exact native action
  rw [step]
  exact StatePrefixEnsures.bind (prefix_entry peer.staged keypair invalid)
    (fun _ => StatePrefixEnsures.bind restored (fun _ => queued))

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations.RestoreEntry
