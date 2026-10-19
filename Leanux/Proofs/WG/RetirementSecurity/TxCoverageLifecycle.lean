import Leanux.Proofs.WG.RetirementSecurity.OccurrenceLifecycle
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageDeviceConfiguration

/-! Device open/down paths preserve resident TX coverage and physical inventory through their actual
staging, timer shutdown and key-unpublication operations. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCovered.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits Native TxCovered.Configuration

theorem initial (net bare : Bool) : Inv [] [] (Runner.initialWG net bare) :=
  ⟨OccurrenceLifecycle.initial net bare,initial_tx_coverage net bare⟩

theorem open_device : Preserves (Inv locals active) wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket_init _)
    | (rx_retention_head sendStagedPackets; exact Native.staged _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv locals active)
       intro x b
       change Preserves (Inv locals active) _)
    | tx_covered_config_step

theorem up : Preserves (Inv locals active) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_device)
    | tx_covered_config_step

theorem stop : Preserves (Inv locals active) wgStop := by
  unfold wgStop requireNotPending
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact join (OccurrenceTimers.purge _) (TxCoverageNative.purge _))
    | (rx_retention_head timersStop; exact Removal.timers_stop _)
    | (rx_retention_head handshakeClear
       exact join
         (RxPollOccurrences.join (KeyMaintenanceCall.erases (.clear _)) (KeyMaintenanceCall.allocation (.clear _))
           (occurrence_passive (OccurrenceKeys.handshake_clear_wire _) (OccurrenceKeys.handshake_clear_queues _)))
         (TxCoverageNative.handshake_clear _))
    | (rx_retention_head keypairsClear
       exact join
         (RxPollOccurrences.join (keypairsClearPrefix_erases _) (keypairsClearPrefix_allocation _)
           (occurrence_passive (OccurrenceKeys.clear_wire _) (OccurrenceKeys.clear_queues _)))
         (TxCoverageNative.clear _))
    | (rx_retention_head resetLastSentHandshake
       exact join
         (RxPollOccurrences.join (KeyMaintenanceCall.erases (.reset _)) (KeyMaintenanceCall.allocation (.reset _))
           (occurrences_queueContents (OccurrenceCreation.reset_wire _) (OccurrenceCreation.reset_contents _)))
         (TxCoverageNative.contents_wire (OccurrenceCreation.reset_contents _) (OccurrenceCreation.reset_wire _)))
    | (rx_retention_head socketReinit; exact socket_reinit _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Inv locals active)
       intro x b
       change Preserves (Inv locals active) _)
    | tx_covered_config_step

theorem down : Preserves (Inv locals active) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop)
    | tx_covered_config_step

end Leanux.Proofs.WG.RetirementSecurity.TxCovered.Lifecycle
