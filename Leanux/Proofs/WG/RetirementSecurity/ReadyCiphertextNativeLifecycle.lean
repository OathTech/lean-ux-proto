import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeDeviceConfiguration

/-! Device open/down paths preserve ready ciphertext coherence through their actual
staging, timer shutdown and key-unpublication operations. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Lifecycle
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity Queues.RxCredits Native ReadyCiphertext.Configuration

theorem initial (net bare : Bool) : Coherent [] [] (Runner.initialWG net bare) :=
  ⟨OccurrenceLifecycle.initial net bare,ReadyCiphertext.initial net bare⟩

theorem open_device : Preserves (Coherent locals active) wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact socket_init _)
    | (rx_retention_head sendStagedPackets; exact send_coherent _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Coherent locals active)
       intro x b
       change Preserves (Coherent locals active) _)
    | ready_ciphertext_config_step

theorem up : Preserves (Coherent locals active) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_device)
    | ready_ciphertext_config_step

theorem stop : Preserves (Coherent locals active) wgStop := by
  unfold wgStop requireNotPending
  simp (config := {zeta := false}) only [branch,unsupported]
  repeat' first
    | (rx_retention_head purgeStagedPackets; exact purge _)
    | (rx_retention_head timersStop; exact Removal.timers_stop _)
    | (rx_retention_head handshakeClear
       exact coherent_join
         (RxPollOccurrences.join (KeyMaintenanceCall.erases (.clear _)) (KeyMaintenanceCall.allocation (.clear _))
           (occurrence_passive (OccurrenceKeys.handshake_clear_wire _) (OccurrenceKeys.handshake_clear_queues _)))
         (handshake_clear _))
    | (rx_retention_head keypairsClear
       exact coherent_join
         (RxPollOccurrences.join (keypairsClearPrefix_erases _) (keypairsClearPrefix_allocation _)
           (occurrence_passive (OccurrenceKeys.clear_wire _) (OccurrenceKeys.clear_queues _)))
         (clear _))
    | (rx_retention_head resetLastSentHandshake
       exact coherent_join
         (RxPollOccurrences.join (KeyMaintenanceCall.erases (.reset _)) (KeyMaintenanceCall.allocation (.reset _))
           (occurrences_queueContents (OccurrenceCreation.reset_wire _) (OccurrenceCreation.reset_contents _)))
         (contents_wire (OccurrenceCreation.reset_contents _) (OccurrenceCreation.reset_wire _)))
    | (rx_retention_head socketReinit; exact socket_reinit _ _)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Coherent locals active)
       intro x b
       change Preserves (Coherent locals active) _)
    | ready_ciphertext_config_step

theorem down : Preserves (Coherent locals active) wgDown := by
  unfold wgDown
  repeat' first
    | (rx_retention_head wgStop; exact stop)
    | ready_ciphertext_config_step

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Lifecycle
