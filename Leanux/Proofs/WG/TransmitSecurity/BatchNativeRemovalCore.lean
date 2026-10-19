import Leanux.Proofs.WG.TransmitSecurity.BatchNativeDeferredWorkers

/-! Original peer-removal drains and timer shutdown preserve alignment.
Their queue resolver and explicit failure paths remain native. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Removal
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity Queues.RxCredits Native Deferred

private theorem fail (stop : Stop) : Preserves P (throw stop : WG.M α) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases run


theorem drain (upTo : Option PeerId) : Preserves (Coherent locals active) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Coherent locals active)
       intro x b
       change Preserves (Coherent locals active) _)
    | (rx_retention_head runFlushedSendWork; exact flushed_send _)
    | (rx_retention_head runFlushedClearWork; exact flushed_clear _)
    | batch_coherent_step


theorem timers_stop (pid : PeerId) : Preserves (Coherent locals active) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Coherent locals active)
       intro x b
       change Preserves (Coherent locals active) _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | (rx_retention_head delTimer; exact maintenance_coherent (.deleteTimer _ _))
    | batch_coherent_step


theorem after_dead (pid : PeerId) : Preserves (Coherent locals active) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Coherent locals active)
       intro x b
       change Preserves (Coherent locals active) _)
    | (rx_retention_head keypairsClear
       exact coherent_join
         (RxPollOccurrences.join (keypairsClearPrefix_erases pid) (keypairsClearPrefix_allocation pid)
           (occurrence_passive (OccurrenceKeys.clear_wire pid) (OccurrenceKeys.clear_queues pid)))
         (clear pid))
    | (rx_retention_head timersStop; exact timers_stop _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | (rx_retention_head peerPut; exact Poll.peer_put _)
    | batch_coherent_step


end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Removal
