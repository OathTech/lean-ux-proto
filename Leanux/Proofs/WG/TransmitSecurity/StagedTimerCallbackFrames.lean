import Leanux.Proofs.WG.TransmitSecurity.StagedNativeTactics

/-! Native timer and send-key maintenance preserve staged occurrence origins.
Purging clears a queue and is handled by its explicit source frame. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
set_option maxHeartbeats 600000

theorem expired_zero (pid : PeerId) : Preserves (Inv h) (expiredZeroKeyMaterial pid) := by
  unfold expiredZeroKeyMaterial
  simp only [peekQueuedUnit,recordQueued]
  repeat' staged_origin_native

theorem fresh_send (pid : PeerId) : Preserves (Inv h) (keepKeyFresh pid) := by
  unfold keepKeyFresh
  repeat' first
    | (rx_retention_head sendQueuedHandshakeInitiation; exact queued _ _)
    | staged_origin_native

end Leanux.Proofs.WG.TransmitSecurity.Staged.Origins.Native
