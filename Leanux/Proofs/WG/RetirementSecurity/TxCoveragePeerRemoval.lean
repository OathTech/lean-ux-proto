import Leanux.Proofs.WG.RetirementSecurity.TxCoverageRemovalCore

/-! Full native peer removal only removes queued batch occurrences; allowed-IP
changes preserve their packet material and retained queue contents. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCovered.Removal
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits Native

theorem allowedips (pid : PeerId) : Preserves (Inv locals active) (removeByPeer pid) :=
  join (OccurrenceAllowedIps.remove pid)
    (TxCoverageNative.contents_wire (OccurrenceAllowedIps.remove_contents pid) (OccurrenceAllowedIps.remove_wire pid))

theorem free_allowedips : Preserves (Inv locals active) WG.free :=
  join OccurrenceAllowedIps.free
    (TxCoverageNative.contents_wire OccurrenceAllowedIps.free_contents OccurrenceAllowedIps.free_wire)

theorem make_dead (pid : PeerId) : Preserves (Inv locals active) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact allowedips _)
    | tx_covered_step


theorem remove (peer : Option PeerId) : Preserves (Inv locals active) (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _)
    | tx_covered_step


theorem remove_all : Preserves (Inv locals active) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact free_allowedips)
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv locals active)
       intro x b
       change Preserves (Inv locals active) _)
    | tx_covered_step


end Leanux.Proofs.WG.RetirementSecurity.TxCovered.Removal
