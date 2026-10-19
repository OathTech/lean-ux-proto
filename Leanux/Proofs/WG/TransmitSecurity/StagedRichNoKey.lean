import Leanux.Proofs.WG.TransmitSecurity.StagedRichCallbacks

/-! The original no-key arm with its actual restoration and nested release
receipts. The held batch returns to the queue before handshake queueing. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes
open AuthenticatedEffects AuthenticatedEffects.CausalJournal
set_option maxHeartbeats 600000

theorem rich_no_key (pid : PeerId) (peer : Peer) (keypair : Option KeypairId) (invalid : Bool) :
    StatePrefixEnsures (Held pid peer) Safe
      (HandshakeSecurity.StagedConservation.Restore.noKeyWith effects stagedRestore
        (HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease) pid peer.staged keypair invalid)
      (fun _ h w _ => Carrier h w) := by
  have tail (kp : Option KeypairId) : StatePrefixEnsures (Held pid peer) Safe
      (do
        effects.step (keypairPut kp false)
        for _ in peer.staged do _ ← effects.step (branch .stagedOrphanWalk true)
        _ ← effects.step (branch .stagedOrphanWalk false)
        stagedRestore pid peer.staged
        HandshakeSecurity.StagedDisposal.Effects.queuedWith effects peerRelease pid false)
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
      exact StatePrefixEnsures.bind (rich_restore pid peer) (fun _ => rich_queued pid false)
  unfold HandshakeSecurity.StagedConservation.Restore.noKeyWith
  dsimp only
  split
  · split
    · apply StatePrefixEnsures.bind (held_read_key _)
      intro key
      exact StatePrefixEnsures.bind (held_write_key _ _) (fun _ => tail _)
    · exact StatePrefixEnsures.bind (held_ambient (AmbientM.invariant "unreachable")) (fun _ => tail _)
  · exact tail _


end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins
