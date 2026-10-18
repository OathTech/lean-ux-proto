import Leanux.Proofs.WG.RetirementSecurity.OccurrenceTimerFrames

/-! Concrete handshake-work draining and the post-dead peer-removal tail
preserve TX owners. Existing native queued-work guards remain observable. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceRemoval
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open Queues.RxCredits OccurrenceStack OccurrenceHandshake OccurrenceDeferred

private theorem fail (stop : Stop) : Preserves P (throw stop : WG.M α) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases run

theorem drain_wire (upTo : Option PeerId) : SameView txCryptWire (drainHandshakeSendWq upTo) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | (rx_retention_head runFlushedSendWork; exact (flushed_send_wire _).wp (· = initial))
    | (rx_retention_head runFlushedClearWork; exact (flushed_clear_wire _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem drain (upTo : Option PeerId) : Preserves (Ready locals active) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Ready locals active)
       intro x b
       change Preserves (Ready locals active) _)
    | (rx_retention_head runFlushedSendWork; exact flushed_send _)
    | (rx_retention_head runFlushedClearWork; exact flushed_clear _)
    | occurrence_ready_step

theorem timers_stop_wire (pid : PeerId) : SameView txCryptWire (timersStop pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold timersStop
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | (rx_retention_head drainHandshakeSendWq; exact (drain_wire _).wp (· = initial))
    | handshake_send_wire initial

theorem timers_stop (pid : PeerId) : Preserves (Ready locals active) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Ready locals active)
       intro x b
       change Preserves (Ready locals active) _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | (rx_retention_head delTimer; exact OccurrenceTimers.maintenance (.deleteTimer _ _))
    | occurrence_ready_step

theorem after_dead_wire (pid : PeerId) : SameView txCryptWire (peerRemoveAfterDead pid) := by
  intro initial
  change Preserves (fun w => txCryptWire w = initial) _
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => txCryptWire w = initial)
       intro x b
       change Preserves (fun w => txCryptWire w = initial) _)
    | (rx_retention_head keypairsClear; exact (OccurrenceKeys.clear_wire _).wp (· = initial))
    | (rx_retention_head timersStop; exact (timers_stop_wire _).wp (· = initial))
    | (rx_retention_head drainHandshakeSendWq; exact (drain_wire _).wp (· = initial))
    | occurrence_handshake_wire initial

theorem after_dead (pid : PeerId) : Preserves (Ready locals active) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Ready locals active)
       intro x b
       change Preserves (Ready locals active) _)
    | (rx_retention_head keypairsClear
       exact RxPollOccurrences.join (keypairsClearPrefix_erases pid)
         (keypairsClearPrefix_allocation pid)
         (occurrence_passive (OccurrenceKeys.clear_wire pid) (OccurrenceKeys.clear_queues pid)))
    | (rx_retention_head timersStop; exact timers_stop _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | (rx_retention_head peerPut; exact RxPollOccurrences.peer_put _)
    | occurrence_ready_step

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceRemoval
