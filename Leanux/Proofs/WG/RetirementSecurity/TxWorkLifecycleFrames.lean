import Leanux.Proofs.WG.RetirementSecurity.TxRunnerSuspended
import Leanux.Proofs.WG.RetirementSecurity.TxCoverageDeviceLifetime

/-! Native lifecycle leaves retain the actual TX service projection. The
socket frame masks socket labels and port only, and the limiter frame masks
only ratelimiter state; neither can erase packet ownership or actor credit. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxWork
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Queues.RxCredits

theorem socket_work {action : WG.M α} (same : SameSocket action) : SameView queued action :=
  same.of_factor (fun s : WGOwnedView=>queued {dev:=s.dev}) queued
    (fun w=>by simp [queued,socketView,socketDevice,wgOwnedView,wgStoreView,Option.map_map,Function.comp_def])

theorem serving_socket_reinit (new4 new6 : Option Nat) :
    Preserves (Serving locals crypt tx) (socketReinit new4 new6) :=
  serving_join (passive_contents (OccurrenceConfiguration.socket_wire (socketReinit_sameSocket new4 new6))
    (OccurrenceConfiguration.socket_contents (socketReinit_sameSocket new4 new6))
    (socket_work (socketReinit_sameSocket new4 new6))) (TxCovered.Configuration.socket_reinit new4 new6)

theorem serving_socket_init (port : Nat) : Preserves (Serving locals crypt tx) (socketInit port) :=
  serving_join (passive_contents (OccurrenceConfiguration.socket_wire (socketInit_sameSocket port))
    (OccurrenceConfiguration.socket_contents (socketInit_sameSocket port))
    (socket_work (socketInit_sameSocket port))) (TxCovered.Configuration.socket_init port)

theorem limiter_wire : SameView txCryptWire ratelimiterUninit :=
  ratelimiterUninit_sameRatelimiter.of_factor (fun s=>txCryptWire {dev:=s.dev}) _ (fun _=>rfl)

theorem serving_limiter : Preserves (Serving locals crypt tx) ratelimiterUninit := by
  apply serving_join
  · exact passive limiter_wire
      (ratelimiterUninit_sameRatelimiter.of_factor (fun s=>handoffTxView {dev:=s.dev}) _ (fun _=>rfl))
      (ratelimiterUninit_sameRatelimiter.of_factor (fun s=>queued {dev:=s.dev}) _ (fun _=>rfl))
  · exact (pinned_const _private.Leanux.Proofs.WG.RetirementSecurity.TxCoverageDeviceLifetime.«0».Leanux.Proofs.WG.RetirementSecurity.TxCovered.Lifecycle.limiter)

theorem serving_handshake_clear (pid : PeerId) : Preserves (Serving locals crypt tx) (handshakeClear pid) :=
  serving_join (passive (OccurrenceKeys.handshake_clear_wire pid)
    (OccurrenceKeys.handshake_clear_queues pid) (handshake_clear_work pid))
    (TxCovered.join
      (RxPollOccurrences.join (KeyMaintenanceCall.erases (.clear pid)) (KeyMaintenanceCall.allocation (.clear pid))
        (occurrence_passive (OccurrenceKeys.handshake_clear_wire pid) (OccurrenceKeys.handshake_clear_queues pid)))
      (TxCoverageNative.handshake_clear pid))

theorem reset_work (pid : PeerId) : SameView queued (resetLastSentHandshake pid) := by
  intro initial
  change Preserves (fun w=>queued w=initial) _
  unfold resetLastSentHandshake
  repeat' key_work_step initial

theorem serving_reset (pid : PeerId) : Preserves (Serving locals crypt tx) (resetLastSentHandshake pid) :=
  serving_join (passive_contents (OccurrenceCreation.reset_wire pid)
    (OccurrenceCreation.reset_contents pid) (reset_work pid))
    (TxCovered.join
      (RxPollOccurrences.join (KeyMaintenanceCall.erases (.reset pid)) (KeyMaintenanceCall.allocation (.reset pid))
        (occurrences_queueContents (OccurrenceCreation.reset_wire pid) (OccurrenceCreation.reset_contents pid)))
      (TxCoverageNative.contents_wire (OccurrenceCreation.reset_contents pid) (OccurrenceCreation.reset_wire pid)))

end Leanux.Proofs.WG.RetirementSecurity.TxWork
