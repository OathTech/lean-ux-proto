import Leanux.Proofs.WG.Queues.HolderAuxDeferred
import Leanux.Proofs.WG.Queues.SlotRemoval

/-! Actual send-work dispatch and its outer waits retain the funded account,
physical ring, owner journal and nullable key-slot compatibility together.
The scheduler uses its concrete receive proof on this same stronger domain. -/
namespace Leanux.Proofs.WG.Queues.RxCredits.HolderAuxSend
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do
open DurableHolders

/-- Selection reads and records do not change WG state. The actual selected
native dequeue/worker/payment run supplies the slot endpoint, including final
peer deletion; no positive-reference or pending-work premise is added. -/
theorem sendOne_slots : Preserves (fun w : World => CurrentSlots.Inv w.wg) Env.runOneSendWorker := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v hi run
  cases result
  obtain ⟨d,head,unit,afterPeek,pid,beforeWorker,_,_,_,_,_,worker⟩ :=
    SendEnvironment.runOneSendWorker_selected w v run
  exact (hoare_iff_run_ambient _ _ _).mp (CurrentSlots.Removal.flushedSend pid)
    w.wg beforeWorker () v.wg v.ambient hi worker

/-- The existing audit retains its exact failure prefix. Funding, owner checks
and slots are joined only at the endpoint of this same normal execution. -/
theorem sendOne (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe
      (RxHistory.audit runOneSendWorkerAudit) := by
  apply HolderAuxiliary.pair
  · exact HolderDeferred.sendOne_preserves initial loans before
  · exact OwnerDeferred.sendOne
  · intro w h hi x v run
    exact (hoare_iff_run _ _ _).mp sendOne_slots w x v hi.2.2
      ((RxHistory.audit_erases runOneSendWorkerAudit_erases w h).symm.trans run)

/-- The actual record budget, source queue selection, paid send worker and
subsequent scheduler all remain in their original order. -/
theorem runSendWorkers (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe RxHistory.runSendWorkers := by
  have safe : ∀ h w, HolderAuxiliary.Inv initial loans before h w → OwnerChecks.Safe h :=
    fun _ _ hi => hi.2.1.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      HolderAuxiliary.Inv initial loans before h w → HolderAuxiliary.Inv initial loans before h v :=
    fun _ _ _ same hi => HolderAuxiliary.store hi same
  unfold RxHistory.runSendWorkers
  repeat' first
    | (scheduler_preserve_at runOneSendWorkerAudit; exact sendOne initial loans before)
    | (scheduler_preserve_at RxHistory.schedule; exact HandshakeWorker.schedule initial loans before _)
    | deferred_raw_steps safe saved

/-- This is the original after-transmit observer, including its mixed-work
rejection, conditional crypt wait and completion guard, then send draining. -/
theorem afterXmit (initial : Ledger) (loans : Reservations) (before : List RxHistory.Event) :
    PrefixPreserves (HolderAuxiliary.Inv initial loans before) OwnerChecks.Safe RxHistory.afterXmit := by
  have safe : ∀ h w, HolderAuxiliary.Inv initial loans before h w → OwnerChecks.Safe h :=
    fun _ _ hi => hi.2.1.safe
  have saved : ∀ h w v, productStoreView v=productStoreView w →
      HolderAuxiliary.Inv initial loans before h w → HolderAuxiliary.Inv initial loans before h v :=
    fun _ _ _ same hi => HolderAuxiliary.store hi same
  unfold RxHistory.afterXmit
  repeat' first
    | (scheduler_preserve_at RxHistory.runCryptWorkers; exact HolderAuxDeferred.crypt initial loans before)
    | (scheduler_preserve_at RxHistory.runSendWorkers; exact runSendWorkers initial loans before)
    | (scheduler_preserve_at requireDrainedPrefix; exact HolderAuxDeferred.drained initial loans before _ _)
    | deferred_raw_steps safe saved

/-- The native dispatch endpoint is paired with the exact original audit
journal, with no state asserted for a stopped execution. -/
theorem sendOne_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : Env.runOneSendWorker.run w=.ok ((),v)) :
    HolderAuxiliary.Inv initial loans before
      (runPrefix (RxHistory.audit runOneSendWorkerAudit) w h).2 v := by
  have actual := (RxHistory.audit_erases runOneSendWorkerAudit_erases w h).trans run
  have post := (sendOne initial loans before w h hi).choose_spec.2.2
  simpa only [actual] using post

theorem runSendWorkers_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : Env.runSendWorkers.run w=.ok ((),v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix RxHistory.runSendWorkers w h).2 v := by
  have actual := (RxHistory.runSendWorkers_erases w h).trans run
  have post := (runSendWorkers initial loans before w h hi).choose_spec.2.2
  simpa only [actual] using post

theorem afterXmit_normal (hi : HolderAuxiliary.Inv initial loans before h w)
    (run : Env.afterXmit.run w=.ok ((),v)) :
    HolderAuxiliary.Inv initial loans before (runPrefix RxHistory.afterXmit w h).2 v := by
  have actual := (RxHistory.afterXmit_erases w h).trans run
  have post := (afterXmit initial loans before w h hi).choose_spec.2.2
  simpa only [actual] using post

end Leanux.Proofs.WG.Queues.RxCredits.HolderAuxSend
