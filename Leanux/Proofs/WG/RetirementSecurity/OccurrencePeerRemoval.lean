import Leanux.Proofs.WG.RetirementSecurity.OccurrenceAllowedIps

/-! Complete native peer removal preserves actual TX ownership, including
all queue flushes and the final peer payment. No blanket reference premise is
needed for this packet-inventory transport. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceRemoval
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceStack OccurrenceHandshake

theorem make_dead_wire (pid : PeerId) : SameView txCryptWire (peerMakeDead pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact (OccurrenceAllowedIps.remove_wire _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem make_dead (pid : PeerId) : Preserves (Ready locals active) (peerMakeDead pid) := by
  unfold peerMakeDead
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head removeByPeer; exact OccurrenceAllowedIps.remove _)
    | occurrence_ready_step

theorem remove_wire (peer : Option PeerId) : SameView txCryptWire (peerRemove peer) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact (make_dead_wire _).wp (· = initial))
    | (rx_retention_head peerRemoveAfterDead; exact (after_dead_wire _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem remove (peer : Option PeerId) : Preserves (Ready locals active) (peerRemove peer) := by
  unfold peerRemove
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _)
    | occurrence_ready_step

theorem remove_all_wire : SameView txCryptWire peerRemoveAll := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact OccurrenceAllowedIps.free_wire.wp (· = initial))
    | (rx_retention_head peerMakeDead; exact (make_dead_wire _).wp (· = initial))
    | (rx_retention_head peerRemoveAfterDead; exact (after_dead_wire _).wp (· = initial))
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | occurrence_handshake_wire initial

theorem remove_all : Preserves (Ready locals active) peerRemoveAll := by
  unfold peerRemoveAll
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head WG.free; exact OccurrenceAllowedIps.free)
    | (rx_retention_head peerMakeDead; exact make_dead _)
    | (rx_retention_head peerRemoveAfterDead; exact after_dead _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Ready locals active)
       intro x b
       change Preserves (Ready locals active) _)
    | occurrence_ready_step

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceRemoval
