import Leanux.Proofs.WG.TransmitSecurity.StagedRichSourceOrigins
import Leanux.Proofs.WG.TransmitSecurity.StagingProcessed

/-! The complete shared staging source preserves occurrence origins. Early
restoration and successful allocation have different intermediate states. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000
set_option pp.structureInstances false

private theorem forget_held {action : WGPrefix Event α}
    (safe : StatePrefixPreserves (Held pid peer) Safe action) :
    StatePrefixEnsures (Held pid peer) Safe action (fun _ h w _ => Carrier h w) :=
  safe.consequence (fun _ _ _ before => before) (fun _ _ _ _ after => after.1)

private def Done (acc : Option Unit × List DataPacket) (h : List Event)
    (w : WGWorld) (_ : Ambient) := Carrier h w ∧ acc.1.isSome = true

theorem staging_observed (pid : PeerId) : StateSafe (Driver.stagingObserved hooks pid) := by
  unfold Driver.stagingObserved
  apply StatePrefixEnsures.bind (selection_observed pid)
  intro chosen
  cases chosen with
  | none =>
    exact StatePrefixEnsures.pure _ (fun _ _ _ before => before.1.2) (fun _ _ _ before => before.1)
  | some pair =>
    obtain ⟨p,kp⟩ := pair
    apply StatePrefixEnsures.consequence (P := Held pid p) (Q := fun _ h w _ => Carrier h w)
    · apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedNoKeypair kp.isNone))
      intro missing
      split
      · exact no_key_observed pid p kp false
      · cases kp with
        | none => exact forget_held (held_ambient (AmbientM.invariant "unreachable"))
        | some id =>
          apply StatePrefixEnsures.bind (held_read_key id)
          intro key
          apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedKeyInvalid !key.sending.isValid))
          intro invalid
          split
          · exact no_key_observed pid p (some id) false
          · apply StatePrefixEnsures.bind (held_world _ (branchExpired_sameWGWorld _ _ _ _))
            intro expired
            split
            · exact no_key_observed pid p (some id) true
            · apply StatePrefixEnsures.bind
              · apply forIn_processed p.staged [] (none,[]) _ (fun _ _ => Held pid p) Done Safe
                  (fun _ _ _ _ _ before => before.1.2) (fun _ _ _ _ before => before.1.2)
                intro packet seen acc
                apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedNonceIterate true))
                intro _
                apply StatePrefixEnsures.bind (held_world _ (ipTunnelEcnEncap_sameWGWorld packet))
                intro ds
                apply StatePrefixEnsures.bind (reserve_observed id)
                intro nonce
                apply StatePrefixEnsures.bind (held_ambient (AmbientM.branchCmp .stagedNonceRejected
                  (nonce ≥ REJECT_AFTER_MESSAGES) nonce REJECT_AFTER_MESSAGES))
                intro rejected
                cases rejected with
                | true =>
                  apply StatePrefixEnsures.bind (no_key_observed pid p (some id) true)
                  intro out
                  exact StatePrefixEnsures.pure _ (fun _ _ _ before => before.2)
                    (fun _ _ _ before => ⟨before,rfl⟩)
                | false => exact held_pure _
              · intro acc
                obtain ⟨done,packets⟩ := acc
                cases done with
                | some out =>
                  exact StatePrefixEnsures.pure _
                    (fun _ _ _ before => before.elim (fun h => h.1.2) (fun h => h.1.2))
                    (fun _ _ _ before => before.elim (fun h => h.1) (fun h => h.1))
                | none =>
                  apply StatePrefixEnsures.consequence (P := Held pid p)
                    (Q := fun _ h w _ => Carrier h w)
                  · apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedNonceIterate false))
                    intro _
                    apply StatePrefixEnsures.bind (held_owner (.keypair id))
                    intro owner
                    apply StatePrefixEnsures.bind (held_peer_get owner)
                    intro _
                    exact (StatePrefixEnsures.bind (allocate_observed packets)
                      (fun items => create_observed pid items)).consequence
                        (fun _ _ _ before => before.1) (fun _ _ _ _ after => after)
                  · intro h w a before
                    rcases before with done | held
                    · simp [Done] at done
                    · exact held
                  · exact fun _ _ _ _ after => after
    · intro h w a before
      exact ⟨before.1,before.2 p kp rfl⟩
    · exact fun _ _ _ _ after => after

theorem keepalive_observed_source (pid : PeerId) : StateSafe (Driver.keepaliveObserved hooks pid) := by
  unfold Driver.keepaliveObserved
  apply StatePrefixEnsures.bind (keepalive_observed pid)
  intro ready
  cases ready
  · exact state_pure _
  · exact staging_observed pid

theorem transmit_observed (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    StateSafe (Driver.transmitObserved hooks family addr packets mtu) := by
  unfold Driver.transmitObserved
  apply StatePrefixEnsures.bind (rich_routing_observed family addr packets mtu)
  intro selected
  cases selected with
  | error err => exact state_pure err
  | ok pid =>
    apply StatePrefixEnsures.bind (staging_observed pid)
    intro _
    exact StatePrefixEnsures.bind (disposal_release_observed (some pid)) (fun _ => state_pure 0)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
