import Leanux.Proofs.WG.TransmitSecurity.StagedQueueFrames

/-! The native no-key arm restores the original selected occurrences before
requesting a handshake. A restored queue is no longer the empty held queue. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000

theorem held_pure (value : α) : StatePrefixPreserves (Held pid peer) Safe (pure value) :=
  StatePrefixEnsures.pure _ (fun _ _ _ before => before.1.2) (fun _ _ _ before => before)

theorem held_loop {α β : Type} (xs : List α) (initial : β)
    (body : α → β → WGPrefix Event (ForInStep β))
    (step : ∀ x b, StatePrefixPreserves (Held pid peer) Safe (body x b)) :
    StatePrefixPreserves (Held pid peer) Safe (forIn xs initial body) :=
  StatePrefixEnsures.forInInvariant xs initial body (fun _ => Held pid peer) Safe
    (fun _ _ _ _ before => before.1.2) step

theorem no_key_observed (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) (invalid : Bool) :
    StatePrefixEnsures (Held pid peer) Safe
      (PacketEffects.noKeyWith effects pid peer.staged keypair invalid)
      (fun _ h w _ => Carrier h w) := by
  have tail (kp : Option KeypairId) : StatePrefixEnsures (Held pid peer) Safe
      (do
        effects.step (keypairPut kp false)
        for _ in peer.staged do _ ← effects.step (branch .stagedOrphanWalk true)
        _ ← effects.step (branch .stagedOrphanWalk false)
        effects.step (HandshakeSecurity.NonceRejection.restore pid peer.staged)
        TimerEffects.queuedWith effects pid false)
      (fun _ h w _ => Carrier h w) := by
    apply StatePrefixEnsures.bind (held_key_put kp false)
    intro _
    apply StatePrefixEnsures.bind
    · apply held_loop
      intro packet acc
      apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedOrphanWalk true))
      intro _
      exact held_pure _
    · intro _
      apply StatePrefixEnsures.bind (held_ambient (AmbientM.branch .stagedOrphanWalk false))
      intro _
      exact StatePrefixEnsures.bind (held_restore pid peer) (fun _ => queued_observed pid false)
  unfold PacketEffects.noKeyWith
  dsimp only
  split
  · split
    · apply StatePrefixEnsures.bind (held_read_key _)
      intro key
      exact StatePrefixEnsures.bind (held_write_key _ _) (fun _ => tail _)
    · exact StatePrefixEnsures.bind (held_ambient (AmbientM.invariant "unreachable")) (fun _ => tail _)
  · exact tail _

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
