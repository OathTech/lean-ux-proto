import Leanux.Proofs.WG.Origins.OwnerStack
import Leanux.Proofs.WG.Origins.OwnerFocus
import Leanux.Proofs.WG.Origins.CurrentWorkers

/-! Receiving-owner checks through the existing persistent poll and worker
journal. All conjuncts concern the same execution and its actual Stop prefix. -/
namespace Leanux.Proofs.WG.OwnerWorkers
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues
open Origins.HistorySupport (sensitive)

theorem store (h : List RxHistory.Event) (w v : World)
    (eq : productStoreView v = productStoreView w) (hi : OwnerChecks.Inv h w) :
    OwnerChecks.Inv h v :=
  ⟨(pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.store)
      h w v eq hi.current,
    hi.boundary.productStore eq,
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConsume.«0».Leanux.Proofs.WG.OwnerConsume.carrier_sameDev)
      hi.carrier (congrArg (fun s : ProductStore43 => s.2.2.2.dev) eq),
    hi.checked⟩

theorem poll (pid : PeerId) (budget : Nat) : OwnerChecks.Preserves (RxHistory.observePoll pid budget) := by
  have quiet : HistoryFrame sensitive (RxHistory.observePoll pid budget) :=
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentPollHistory.«0».Leanux.Proofs.WG.CurrentPoll.observed_frame)
      sensitive (by intro e; cases e <;> rfl) pid budget
  apply OwnerChecks.quiet _ (RxHistory.observePoll_appends pid budget) quiet
    (CurrentPoll.checked pid budget) (RxHistory.observePoll_preserves pid budget)
  intro w h hi x v hr
  exact (hoare_iff_run _ _ _).mp (OwnerStack.poll_stack pid budget) w x v hi.carrier
    ((RxHistory.observePoll_erases pid budget w h).symm.trans hr)

private theorem pending : OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver RxNapi.pendingPrefix)) := by
  apply OwnerChecks.native_quiet _ RxNapi.pendingSource (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.pending_erases))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      sensitive (fun _ => rfl) _)
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.pending)
    (RxHistory.mixed_preserves RxNapi.pending_preserves.liftWGObserver)
  intro history
  apply hoare_consequence (show Preserves OwnerBounds.Carrier RxNapi.pendingSource from by
    unfold RxNapi.pendingSource
    repeat' owner_control_step)
    (fun _ hi => hi.2) (fun _ _ hi => hi)

private theorem scheduled : OwnerChecks.Preserves (RxHistory.mixed (liftWGObserver RxNapi.scheduledPrefix)) := by
  apply OwnerChecks.native_quiet _ RxNapi.scheduledSource (Appends.focus _ _ _)
    (RxHistory.mixed_erases (liftWGObserver_erases RxNapi.scheduled_erases))
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      sensitive (fun _ => rfl) _)
    (pinned_const _private.Leanux.Proofs.WG.Origins.CurrentWorkers.«0».Leanux.Proofs.WG.CurrentWorkers.scheduled)
    (RxHistory.mixed_preserves RxNapi.scheduled_preserves.liftWGObserver)
  intro history
  apply hoare_consequence (show Preserves OwnerBounds.Carrier RxNapi.scheduledSource from by
    unfold RxNapi.scheduledSource
    repeat' owner_control_step)
    (fun _ hi => hi.2) (fun _ _ hi => hi)

theorem napiSoftirq : OwnerChecks.Preserves RxHistory.napiSoftirq :=
  RxNapi.softirq_preserves (fun _ _ hi => hi.safe) store pending poll

theorem pollScheduledInline : OwnerChecks.Preserves RxHistory.pollScheduledInline :=
  RxNapi.inline_preserves (fun _ _ hi => hi.safe) store pending poll

theorem napiIrqExit : OwnerChecks.Preserves RxHistory.napiIrqExit :=
  RxNapi.irqExit_preserves (fun _ _ hi => hi.safe) store scheduled napiSoftirq

end Leanux.Proofs.WG.OwnerWorkers
