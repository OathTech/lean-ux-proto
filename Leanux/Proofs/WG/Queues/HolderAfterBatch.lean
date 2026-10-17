import Leanux.Proofs.WG.Queues.HolderAuxSend
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation

/-! The actual batch wait and inline NAPI scan retain the complete auxiliary
account on the original receive journal. No fresh admission is hidden here:
the caller supplies the funded state at the beginning of this same wait. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderAfterBatch
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

/-- The exact source factor retains both record-driven and placeholder paths,
including budget exhaustion, concrete scheduling and the final drained test. -/
theorem afterBatch (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe RxHistory.afterBatch := by
  rw [TrafficSource.afterBatch_factor]
  exact TrafficSource.afterBatch_preserves
    (I := HolderAuxiliary.Inv initial loans before) (S := OwnerChecks.Safe)
    (fun _ _ hi => hi.2.1.safe) (fun _ _ _ same hi => HolderAuxiliary.store hi same)
    _ _ _ _ _ (HolderAuxDeferred.crypt initial loans before)
    (HolderAuxSend.runSendWorkers initial loans before) (HolderAuxSend.sendOne initial loans before)
    (HandshakeWorker.schedule initial loans before) (HolderAuxDeferred.drained initial loans before)

theorem afterBatch_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : Env.afterBatch.run w=.ok ((),v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix RxHistory.afterBatch w h).2 v := by
  have actual := (RxHistory.afterBatch_erases w h).trans run
  have post := (afterBatch initial loans before w h hi).choose_spec.2.2
  simpa only [actual] using post

/-- Actual inline polling retains the physical decrypt ring. The stack callback
is the existing complete product callback, which may send or delete peers. -/
theorem inline_cell : SameView RxRing.cell Env.pollScheduledInline := by
  have poll := fun pid => RxRing.rxPoll_cell pid NAPI_POLL_WEIGHT _ RxRing.stackForM_cell
  ring_poll_source [Env.pollScheduledInline] using [poll] with []

/-- The funded ledger follows precisely the scan's promoted removal suffix;
physical, owner and slot conclusions use that identical original execution. -/
theorem inlinePoll (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe RxHistory.pollScheduledInline := by
  apply HolderAuxiliary.pair
  · apply (pinned_const _private.Leanux.Proofs.WG.Queues.HolderScheduler.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler.combine)
      (HolderNapi.inline_preserves initial loans before) RxHistory.pollScheduledInline_erases
    intro w x v hi run
    exact (pinned_const _private.Leanux.Proofs.WG.Queues.HolderScheduler.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderScheduler.physical_cell)
      hi ((ProjectedAction.iff_run _ _ _).mp inline_cell w x v run)
  · exact OwnerWorkers.pollScheduledInline
  · intro w h hi x v run
    have slots := (CurrentSlots.inline_observed w h hi.2.2).choose_spec.2.2
    simpa only [run] using slots

theorem inlinePoll_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : Env.pollScheduledInline.run w=.ok ((),v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix RxHistory.pollScheduledInline w h).2 v := by
  have actual := (RxHistory.pollScheduledInline_erases w h).trans run
  have post := (inlinePoll initial loans before w h hi).choose_spec.2.2
  simpa only [actual] using post

end Leanux.Proofs.WG.Queues.RxCredits.HolderAfterBatch
