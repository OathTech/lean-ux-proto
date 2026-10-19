import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationRestoreObserved
import Leanux.Proofs.WG.HandshakeSecurity.NonceRejectionFrames
import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDecoration
import Leanux.Proofs.WG.AuthenticatedEffects.PacketEffectsProjection

/-! The same no-key source with the whole-batch restoration exposed before
handshake queueing. All rejection arms use this one cut; restoration is neither
a new packet birth nor a disposal. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects

theorem native_factor [Monad m] (o : TimerEffects.Ops m)
    (pid : PeerId) (packets : List Packet) (keypair : Option KeypairId) (invalid : Bool) :
    noKeyWith o (fun pid packets => o.step (NonceRejection.restore pid packets))
      (TimerEffects.queuedWith o) pid packets keypair invalid =
      PacketEffects.noKeyWith o pid packets keypair invalid := rfl

/-- The full native batch is returned at the head of the resident queue;
its actual disposal counter is unchanged. -/
theorem Receipt.Valid.effects (r : Receipt) (valid : r.Valid) :
    ∃ d peer, r.run.before.dev = some d ∧ d.peers[r.pid]? = some peer ∧
      r.run.after.dev = some {d with peers := d.peers.insert r.pid {peer with staged := r.packets ++ peer.staged}} ∧
      NonceRejection.dropped r.run.after = NonceRejection.dropped r.run.before :=
  NonceRejection.restoration r.pid r.packets r.run valid

end Leanux.Proofs.WG.HandshakeSecurity.StagedConservation.Restore
