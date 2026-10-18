import Leanux.Proofs.WG.Origins.OwnerAllowedIps
import Leanux.Proofs.WG.Origins.OwnerLifecycle

/-! The concrete dead-marking, work drains and reference releases preserve
receiving-owner bounds. Crypt-work rejection remains an actual source Stop. -/
namespace Leanux.Proofs.WG.OwnerRemoval
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues OwnerBounds OwnerControls OwnerLifecycle

theorem peerMakeDead_preserves (pid : PeerId) : Preserves Carrier (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (allocation_release_head removeByPeer; exact OwnerAllowedIps.removeByPeer_preserves _)
    | owner_lifecycle_step

theorem peerRemoveAfterDead_preserves (pid : PeerId) : Preserves Carrier (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (allocation_release_head keypairsClear; exact keypairsClear_preserves _)
    | (allocation_release_head timersStop; exact timersStop_preserves _)
    | (allocation_release_head drainHandshakeSendWq; exact drainHandshakeSendWq_preserves _)
    | owner_lifecycle_step

theorem peerRemove_preserves (peer : Option PeerId) : Preserves Carrier (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (allocation_release_head peerMakeDead; exact peerMakeDead_preserves _)
    | (allocation_release_head peerRemoveAfterDead; exact peerRemoveAfterDead_preserves _)
    | owner_lifecycle_step

end Leanux.Proofs.WG.OwnerRemoval
