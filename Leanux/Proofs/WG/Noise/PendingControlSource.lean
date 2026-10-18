import Leanux.Proofs.WG.Noise.PendingTicketControlFrames
import Leanux.Proofs.WG.Noise.PendingObserverSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.PendingReception
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues ConfiguredReceive

theorem native_socket {α : Type} (action : WG.M α) (frame : SameSocket action) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) action :=
  native_preserves action
    ((pinned_const _private.Leanux.Proofs.WG.Queues.DeviceAuxEntry.«0».Leanux.Proofs.WG.Queues.RxCredits.DeviceAuxEntry.configured_socket) frame)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotDevice.«0».Leanux.Proofs.WG.CurrentSlots.Device.socket) frame)
    (PendingTickets.retained_of_frame (PendingTickets.frame_socket action frame)) seen

theorem staged (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) (sendStagedPackets pid) :=
  native_preserves _ (ConfiguredTraffic.staged pid) (CurrentSlots.sendStagedPackets_preserves pid)
    (PendingTickets.sendStagedPackets_retained pid) seen

/-- Actual open includes the socket-error return and the saved peer loop. -/
theorem open_native (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) wgOpen := by
  unfold wgOpen
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head socketInit; exact native_socket _ (socketInit_sameSocket _) seen)
    | (rx_retention_head sendStagedPackets; exact staged _ seen)
    | (rx_retention_head sendKeepalive; exact keepalive _ seen)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (fun w => PendingSession.NativeInv w seen)
       intro x acc
       change Preserves (fun w => PendingSession.NativeInv w seen) _)
    | pending_native_step seen

theorem up_native (seen : List Nat) :
    Preserves (fun w => PendingSession.NativeInv w seen) wgUp := by
  unfold wgUp
  repeat' first
    | (rx_retention_head wgOpen; exact open_native seen)
    | pending_native_step seen

end Leanux.Proofs.WG.Noise.PendingReception

namespace Leanux.Proofs.WG.Noise.PendingSession
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues

/-- Audit-only observers cannot add confirmation labels, even when they stop. -/
theorem audit_observed {α : Type} (g : AuditM α) (action : Leanux.M α)
    (erases : ErasesPrefix g action)
    (normal : ∀ seen, Preserves (fun w : World => NativeInv w.wg seen) action) :
    PrefixPreserves StateInv HistorySafe (RxHistory.audit g) :=
  observer _ _ (Appends.focus _ _ _) (RxHistory.audit_erases erases)
    (focusPrefix_other RxHistory.Event.audit RxHistory.auditEvent CounterConsume.eventLabel
      (by intro e; rfl) g) normal

theorem mixed_observed {α : Type} (g : PrefixM LifetimeEvent α) (action : Leanux.M α)
    (erases : ErasesPrefix g action)
    (normal : ∀ seen, Preserves (fun w : World => NativeInv w.wg seen) action) :
    PrefixPreserves StateInv HistorySafe (RxHistory.mixed g) :=
  audit_observed (auditFocus g) action (auditFocus_erases erases) normal

theorem lifecycle_observed {α : Type} (g : MixedM α) (action : WG.M α)
    (erases : ErasesStatePrefix g action)
    (normal : ∀ seen, Preserves (fun w => NativeInv w seen) action) :
    PrefixPreserves StateInv HistorySafe (RxHistory.mixed (liftWGObserver g)) :=
  mixed_observed _ _ (liftWGObserver_erases erases) (native_product action normal)

theorem create_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver wgCreatePrefix)) :=
  lifecycle_observed _ _ wgCreatePrefix_erases
    (fun seen => (ensures_iff _ _ _).mp (create seen))

theorem destruct_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver wgDestructPrefix)) :=
  lifecycle_observed _ _ wgDestructPrefix_erases
    (fun seen => (ensures_iff _ _ _).mp (destruct seen))

theorem stop_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver wgStopPrefix)) :=
  lifecycle_observed _ _ wgStopPrefix_erases stop

theorem down_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver wgDownPrefix)) :=
  lifecycle_observed _ _ wgDownPrefix_erases down

theorem open_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver wgOpenPrefix)) :=
  lifecycle_observed _ _ wgOpenPrefix_erases PendingReception.open_native

theorem up_observed : PrefixPreserves StateInv HistorySafe
    (RxHistory.mixed (liftWGObserver wgUpPrefix)) :=
  lifecycle_observed _ _ wgUpPrefix_erases PendingReception.up_native

end Leanux.Proofs.WG.Noise.PendingSession
