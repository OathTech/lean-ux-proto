import Leanux.Proofs.WG.RetirementSecurity.HolderScheduler
import Leanux.Proofs.WG.RetirementSecurity.HandshakeSendDispatch
import Leanux.Proofs.WG.Queues.HolderAuxTimers

/-! Original send-work and crypt waits carry the exact key ledger alongside
the existing peer account. Actual selected work pays its own peer occurrence;
live configured slots retain a separate anchor before that payment. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem send_one : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.audit runOneSendWorkerAudit) := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HolderAuxSend.sendOne initial loans before w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix (RxHistory.audit runOneSendWorkerAudit) w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have native := (RxHistory.audit_erases runOneSendWorkerAudit_erases w h).symm.trans run
    cases result:out.1
    have actual : Env.runOneSendWorker.run w=.ok ((),out.2) := by simpa only [result] using native
    obtain ⟨fresh,hist,holders,funded,stable⟩ := entry.1.1.1
    have anchors := KeySlotLiveness.references entry.2.2.2.2 funded entry.2.2.2.1
      (HolderAuxiliary.owner_configured entry.1.2.1)
    have structural := (ProjectedAction.iff_run _ _ _).mp
      (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.sendOne_view)
      w () out.2 actual
    exact ⟨post,entry.2.1.dispatched_send funded stable anchors actual,
      (hoare_iff_run _ _ _).mp OccurrenceDeferred.send_one w () out.2 entry.2.2.1 actual,
      BaseCoherence.transport entry.2.2.2.1 structural,
      (hoare_iff_run _ _ _).mp (KeySlotDeferred.send_one (pending:=[])) w () out.2 entry.2.2.2.2 actual⟩

theorem clear_one : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.audit runOneClearWorkerAudit) := by
  apply join_native
    (pinned_const _private.Leanux.Proofs.WG.Queues.HolderAuxTimers.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderAuxTimers.clearOne)
    (RxHistory.audit_erases runOneClearWorkerAudit_erases)
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  cases result
  have structural := (ProjectedAction.iff_run _ _ _).mp
    (pinned_const _private.Leanux.Proofs.WG.Queues.BaseCoherenceDeferred.«0».Leanux.Proofs.WG.Queues.RxCredits.BaseCoherence.clearOne_view)
    w () v run
  exact ⟨(entry.1.dispatched_zero run).1,
    (hoare_iff_run _ _ _).mp OccurrenceDeferred.clear_one w () v entry.2.1 run,
    BaseCoherence.transport entry.2.2.1 structural,
    (hoare_iff_run _ _ _).mp (KeySlotDeferred.clear_one (pending:=[])) w () v entry.2.2.2 run⟩

theorem crypt : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe RxHistory.runCryptWorkers := by
  rw [RxHistory.DeferredSource.crypt_factor]
  exact RxHistory.DeferredSource.crypt_preserves (I:=Inv initial loans before temporary locals active)
    (fun _ _ entry=>entry.1.2.1.safe) (fun _ _ _ same entry=>store entry same) _ (schedule none)

theorem drained (what : String) (flags : List Bool) : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe
    (RxHistory.mixed (requireDrainedPrefix what flags)) := by
  apply join_native (HolderAuxDeferred.drained initial loans before what flags)
    (RxHistory.mixed_erases (requireDrainedPrefix_erases what flags))
  apply (hoare_iff_run _ _ _).mpr
  intro w result v entry run
  cases result
  exact (requireDrained_normal what flags w v run).1 ▸ entry

theorem send_all : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe RxHistory.runSendWorkers := by
  have safe : ∀ h w,Inv initial loans before temporary locals active h w→OwnerChecks.Safe h :=
    fun _ _ entry=>entry.1.2.1.safe
  have saved : ∀ h w v,productStoreView v=productStoreView w→
      Inv initial loans before temporary locals active h w→Inv initial loans before temporary locals active h v :=
    fun _ _ _ same entry=>store entry same
  unfold RxHistory.runSendWorkers
  repeat' first
    | (scheduler_preserve_at runOneSendWorkerAudit; exact send_one)
    | (scheduler_preserve_at RxHistory.schedule; exact schedule _)
    | deferred_raw_steps safe saved

theorem after_xmit : PrefixPreserves
    (Inv initial loans before temporary locals active) OwnerChecks.Safe RxHistory.afterXmit := by
  have safe : ∀ h w,Inv initial loans before temporary locals active h w→OwnerChecks.Safe h :=
    fun _ _ entry=>entry.1.2.1.safe
  have saved : ∀ h w v,productStoreView v=productStoreView w→
      Inv initial loans before temporary locals active h w→Inv initial loans before temporary locals active h v :=
    fun _ _ _ same entry=>store entry same
  unfold RxHistory.afterXmit
  repeat' first
    | (scheduler_preserve_at RxHistory.runCryptWorkers; exact crypt)
    | (scheduler_preserve_at RxHistory.runSendWorkers; exact send_all)
    | (scheduler_preserve_at requireDrainedPrefix; exact drained _ _)
    | deferred_raw_steps safe saved

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
