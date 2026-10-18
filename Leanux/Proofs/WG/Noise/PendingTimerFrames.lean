import Leanux.Proofs.WG.Noise.PendingDeviceConfigurationFrames
import Leanux.Proofs.WG.Queues.SlotTimers
import Leanux.Proofs.WG.TimerDiscipline.SectionFrames
import Leanux.Proofs.WG.Noise.PendingSchedulerFrames

set_option autoImplicit false

namespace Leanux.Proofs.WG.Noise.PendingTimers
open Leanux Leanux.WG Lifetimes Queues Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open PendingReception PendingSession

theorem del_native (pid : PeerId) (timer : PeerTimer) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (delTimer pid timer) :=
  native_view _ (ConfiguredIdentity.delTimer_view pid timer)
    (CurrentSlots.delTimer_preserves pid timer) (PendingTickets.delTimer_frame pid timer) seen

theorem mod_native (site : HiddenSite) (pid : PeerId) (timer : PeerTimer)
    (delay : Nat) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (modPeerTimer site pid timer delay) :=
  native_view _ (ConfiguredIdentity.modPeerTimer_view site pid timer delay)
    (CurrentSlots.modPeerTimer_preserves site pid timer delay)
    (PendingTickets.modPeerTimer_frame site pid timer delay) seen

theorem purge_native (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (purgeStagedPackets pid) :=
  native_view _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentDevice.«0».Leanux.Proofs.WG.CurrentLifecycle.purgeStaged_view) pid)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.SlotTimers.«0».Leanux.Proofs.WG.CurrentSlots.Timer.purge) pid)
    (PendingTickets.purgeStagedPackets_frame pid) seen

theorem queued_native (pid : PeerId) (retry : Bool) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (sendQueuedHandshakeInitiation pid retry) :=
  native_preserves _ (ConfiguredTraffic.queued pid retry)
    (CurrentSlots.sendQueuedHandshakeInitiation_preserves pid retry)
    (PendingTickets.sendQueuedHandshakeInitiation_retained pid retry) seen

theorem peerGet_native (pid : PeerId) (seen : List Nat) :
    Preserves (fun w => NativeInv w seen) (peerGet pid) :=
  native_view _ (RxCredits.CreationLoan.peerGet_configured_view pid)
    (CurrentSlots.fields_preserves (project := id) (CurrentSlots.peerGet_fields pid))
    (PendingTickets.frame_from_fields (CurrentSlots.peerGet_fields pid)
      (Keypairs.WGFrames.peerGet_sameSnapshot pid)) seen

theorem timer_section (worker : Worker) (body : Leanux.M Unit) (seen : List Nat)
    (normal : Preserves (fun w : World => NativeInv w.wg seen) body) :
    Preserves (fun w : World => NativeInv w.wg seen) (Env.runTimerSection worker body) :=
  TimerDiscipline.runTimerSection_kernel_contract worker body
    (fun wg _ _ _ => NativeInv wg seen) (fun wg _ _ _ => NativeInv wg seen) normal

private theorem ambient {α : Type} (action : AmbientM α) (seen : List Nat) :
    Preserves (fun w : World => NativeInv w.wg seen) (liftAmbient action) :=
  productAmbient_spec action _ (fun _ _ hi => hi)

macro "pending_timer_product_step " seen:term : tactic => `(tactic| first
  | (rx_retention_head Env.timerWorker; exact PendingScheduler.product_store _ (timerWorker_sameKernel _) $seen)
  | (rx_retention_head Env.requireStepComplete; exact PendingScheduler.product_store _ (PendingScheduler.requireStepComplete_store _) $seen)
  | (rx_retention_head getWG; exact PendingScheduler.product_store _ (fun initial => productGetWG_spec (fun s => s = initial)) $seen)
  | (rx_retention_head modifyWG; exact PendingScheduler.product_store _ (fun initial =>
      productModifyWG_spec (fun s => s = initial) _ (fun _ => rfl)) $seen)
  | (rx_retention_head throw; exact hoare_throw _)
  | (allocation_release_lift_from AmbientM; exact ambient _ $seen)
  | rx_retention_step)

end Leanux.Proofs.WG.Noise.PendingTimers
