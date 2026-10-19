import Leanux.Proofs.WG.Packets.PublicationRemoval

/-! The existing lifetime-only removal observers retain packet certificates
at their actual normal endpoints and preserve their full failed journals.
No new operational observer or alternate execution is introduced. -/
namespace Leanux.Proofs.WG.PublicationFrontier
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

theorem removalCall_checked (call : PeerRemovalCall)
    :
    PrefixPreserves (fun h w => OwnerChecks.Inv h w ∧ Inv h w.wg) OwnerChecks.Safe
      (RxHistory.mixed (liftWGObserver call.observed)) := by
  apply observed_native _ _
    (RxHistory.mixed_erases (liftWGObserver_erases call.erases))
  · apply OwnerChecks.native_mixed _ _ call.erases call.allocation
    · cases call with
      | sendWork pid => exact Origins.Retaining.runFlushedSendWork_material pid
      | clearWork pid => exact Origins.Retaining.runFlushedClearWork_material pid
      | drain upTo => exact Origins.Retaining.drainHandshakeSendWq_material upTo
      | stopTimers pid => exact Origins.Retaining.timersStop_material pid
      | afterDead pid => exact Origins.Retaining.peerRemoveAfterDead_material pid
      | remove peer => exact Origins.Retaining.peerRemove_material peer
      | removeAll => exact Origins.Retaining.peerRemoveAll_material
    · intro history
      cases call with
      | sendWork pid => exact CurrentLifecycle.runFlushedSendWork_preserves pid history
      | clearWork pid => exact CurrentLifecycle.runFlushedClearWork_preserves pid history
      | drain upTo => exact CurrentLifecycle.drainHandshakeSendWq_preserves upTo history
      | stopTimers pid => exact CurrentLifecycle.timersStop_preserves pid history
      | afterDead pid => exact CurrentLifecycle.peerRemoveAfterDead_preserves pid history
      | remove peer => exact CurrentLifecycle.peerRemove_preserves peer history
      | removeAll => exact CurrentLifecycle.peerRemoveAll_preserves history
    · intro history
      apply hoare_consequence (P := OwnerBounds.Carrier) (Q := fun _ w => OwnerBounds.Carrier w) ?_
        (fun _ hi => hi.2) (fun _ _ hi => hi)
      cases call with
      | sendWork pid => exact OwnerLifecycle.runFlushedSendWork_preserves pid
      | clearWork pid => exact OwnerLifecycle.runFlushedClearWork_preserves pid
      | drain upTo => exact OwnerLifecycle.drainHandshakeSendWq_preserves upTo
      | stopTimers pid => exact OwnerLifecycle.timersStop_preserves pid
      | afterDead pid => exact OwnerRemoval.peerRemoveAfterDead_preserves pid
      | remove peer => exact OwnerRemoval.peerRemove_preserves peer
      | removeAll => exact OwnerDevice.peerRemoveAll_preserves
  · intro history
    exact removalCall_preserves call history

end Leanux.Proofs.WG.PublicationFrontier
