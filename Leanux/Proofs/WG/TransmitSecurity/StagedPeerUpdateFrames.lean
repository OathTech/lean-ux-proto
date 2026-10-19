import Leanux.Proofs.WG.TransmitSecurity.StagedNativeTactics

/-! A native saved-peer metadata update retains provenance and returns the
actual prior peer value for its continuation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem update_return (pid : PeerId) (f : Peer → Peer)
    (same : ∀ p, (f p).internalId = p.internalId ∧ (f p).staged = p.staged) :
    Preserves (Inv h) (do let p ← getPeer pid; setPeer pid (f p); pure p) := by
  apply frame
  · exact PacketOrigins.epoch_ring ((TxRing.getPeer_frame pid).bind (fun p =>
      (TxRing.setPeer_frame pid (f p)).bind (fun _ => SameView.pure _ _)))
  · intro initial
    let P := fun queues : PeerId → Option (Nat × List Packet) =>
      ∀ q value, queues q = some value → stagedAt initial q = some value
    apply hoare_bind _ _ (Staged.read_saved P pid)
    intro peer
    have write := Staged.write_saved P pid (f peer)
    rw [(same peer).1,(same peer).2] at write
    exact hoare_bind _ _ write (fun _ => preserves_pure peer)

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
