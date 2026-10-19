import Leanux.Proofs.WG.TransmitSecurity.BatchNativeRemovalCore

/-! Full native peer removal only removes queued batch occurrences; allowed-IP
changes preserve their packet material and retained queue contents. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Removal
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits Native

theorem allowedips (pid : PeerId) : Preserves (Coherent locals active) (removeByPeer pid) :=
  coherent_join (OccurrenceAllowedIps.remove pid)
    (contents_wire (OccurrenceAllowedIps.remove_contents pid) (OccurrenceAllowedIps.remove_wire pid))

theorem free_allowedips : Preserves (Coherent locals active) WG.free :=
  coherent_join OccurrenceAllowedIps.free
    (contents_wire OccurrenceAllowedIps.free_contents OccurrenceAllowedIps.free_wire)

theorem make_dead (pid : PeerId) : Preserves (Coherent locals active) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact allowedips _)
    | batch_coherent_step


theorem remove (peer : Option PeerId) : Preserves (Coherent locals active) (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _)
    | batch_coherent_step


theorem remove_all : Preserves (Coherent locals active) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact free_allowedips)
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Coherent locals active)
       intro x b
       change Preserves (Coherent locals active) _)
    | batch_coherent_step


end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Removal
