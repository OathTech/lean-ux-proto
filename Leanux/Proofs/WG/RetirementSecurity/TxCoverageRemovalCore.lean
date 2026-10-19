import Leanux.Proofs.WG.RetirementSecurity.TxCoverageCoherent

/-! Original peer-removal drains and timer shutdown preserve resident TX coverage.
Their queue resolver and explicit failure paths remain native. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCovered.Removal
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits Native

private theorem fail (stop : Stop) : Preserves P (throw stop : WG.M α) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  cases run


theorem drain (upTo : Option PeerId) : Preserves (Inv locals active) (drainHandshakeSendWq upTo) := by
  unfold drainHandshakeSendWq
  simp (config := {zeta := false}) only
    [Std.Legacy.Range.forIn_eq_forIn_range',peekUnit,resolveUnit,getAmbient,invariant]
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv locals active)
       intro x b
       change Preserves (Inv locals active) _)
    | (rx_retention_head runFlushedSendWork; exact join (OccurrenceDeferred.flushed_send _) (TxCoverageDeferred.flushed_send _))
    | (rx_retention_head runFlushedClearWork; exact join (OccurrenceDeferred.flushed_clear _) (TxCoverageDeferred.flushed_clear _))
    | tx_covered_step


theorem timers_stop (pid : PeerId) : Preserves (Inv locals active) (timersStop pid) := by
  unfold timersStop
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv locals active)
       intro x b
       change Preserves (Inv locals active) _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | (rx_retention_head delTimer; exact maintenance (.deleteTimer _ _))
    | tx_covered_step


theorem after_dead (pid : PeerId) : Preserves (Inv locals active) (peerRemoveAfterDead pid) := by
  unfold peerRemoveAfterDead
  simp (config := {zeta := false}) only [branch,unsupported,invariant]
  repeat' first
    | (rx_retention_head throw; exact fail _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv locals active)
       intro x b
       change Preserves (Inv locals active) _)
    | (rx_retention_head keypairsClear
       exact join
         (RxPollOccurrences.join (keypairsClearPrefix_erases pid) (keypairsClearPrefix_allocation pid)
           (occurrence_passive (OccurrenceKeys.clear_wire pid) (OccurrenceKeys.clear_queues pid)))
         (TxCoverageNative.clear pid))
    | (rx_retention_head timersStop; exact timers_stop _)
    | (rx_retention_head drainHandshakeSendWq; exact drain _)
    | (rx_retention_head peerPut; exact Native.peer_put _)
    | tx_covered_step


end Leanux.Proofs.WG.RetirementSecurity.TxCovered.Removal
