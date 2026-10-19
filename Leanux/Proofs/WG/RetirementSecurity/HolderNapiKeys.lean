import Leanux.Proofs.WG.RetirementSecurity.HolderPoll
import Leanux.Proofs.WG.Queues.HolderNapi

/-! The actual pending/scheduled NAPI scans carry exact key credit and the
native poll support over the same fresh-removal journal used by campaign 1. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderNapiKeys
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

def Inv (sessions : List SessionOrigin.Receipt) (locals : List TxLocalBatch)
    (active : List (List SkbId)) (temporary : Credits.Ledger) (initial : Ledger) (loans : Reservations)
    (before h : List RxHistory.Event) (w : World) :=
  HolderNapi.At initial loans before h w ∧ HolderAccount temporary w.wg ∧
    HolderPoll.Support sessions locals active w.wg

theorem store (entry : Inv sessions locals active temporary initial loans before h w)
    (same : productStoreView v=productStoreView w) : Inv sessions locals active temporary initial loans before h v :=
  ⟨HolderNapi.store entry.1 same,
    HolderPoll.keys_store entry.2.1 (congrArg (fun s:ProductStore43=>s.2.2.2) same),
    HolderPoll.support_store entry.2.2 (congrArg (fun s:ProductStore43=>s.2.2.2) same)⟩

theorem poll (pid budget : Nat) :
    PrefixPreserves (Inv sessions locals active temporary initial loans before) (fun _=>True)
      (RxHistory.observePoll pid budget) := by
  apply NapiCarrier.normal_spec (RxHistory.observePoll_appends pid budget)
  intro w h result v entry run
  have post := (HolderNapi.observePoll_preserves initial loans before pid budget w h entry.1).choose_spec.2.2
  rw [run] at post
  obtain ⟨suffix,history,funded⟩ := entry.1
  have native := (RxHistory.observePoll_erases pid budget w h).symm.trans run
  exact ⟨post,HolderPoll.normal pid budget funded entry.2.1 entry.2.2 native⟩

theorem audit_frame (action : AuditM α) (native : Leanux.M α)
    (erases : ErasesPrefix action native) (same : SameProductStore native) :
    PrefixPreserves (Inv sessions locals active temporary initial loans before) (fun _=>True) (RxHistory.audit action) := by
  apply NapiCarrier.normal_spec (Appends.focus _ _ _)
  intro w h result v entry run
  change (runPrefix (RxHistory.audit action) w h).1=.ok (result,v) at run
  have post := (HolderNapi.audit_frame action native erases same w h entry.1).choose_spec.2.2
  rw [run] at post
  exact ⟨post,HolderPoll.product_store same entry.2 ((RxHistory.audit_erases erases w h).symm.trans run)⟩

theorem softirq : PrefixPreserves (Inv sessions locals active temporary initial loans before)
    (fun _=>True) RxHistory.napiSoftirq := by
  unfold RxHistory.napiSoftirq
  apply RxNapi.softirq_preserves (I:=Inv sessions locals active temporary initial loans before)
    (fun _ _ _=>True.intro) (fun _ _ _ same entry=>store entry same)
  · exact audit_frame _ _ (auditFocus_erases (liftWGObserver_erases RxNapi.pending_erases))
      (pinned_const _private.Leanux.Proofs.WG.Queues.HolderNapi.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderNapi.pending_store)
  · exact poll

theorem inline : PrefixPreserves (Inv sessions locals active temporary initial loans before)
    (fun _=>True) RxHistory.pollScheduledInline := by
  unfold RxHistory.pollScheduledInline
  apply RxNapi.inline_preserves (I:=Inv sessions locals active temporary initial loans before)
    (fun _ _ _=>True.intro) (fun _ _ _ same entry=>store entry same)
  · exact audit_frame _ _ (auditFocus_erases (liftWGObserver_erases RxNapi.pending_erases))
      (pinned_const _private.Leanux.Proofs.WG.Queues.HolderNapi.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderNapi.pending_store)
  · exact poll

theorem irq : PrefixPreserves (Inv sessions locals active temporary initial loans before)
    (fun _=>True) RxHistory.napiIrqExit := by
  unfold RxHistory.napiIrqExit
  apply RxNapi.irqExit_preserves (I:=Inv sessions locals active temporary initial loans before)
    (fun _ _ _=>True.intro) (fun _ _ _ same entry=>store entry same)
  · exact audit_frame _ _ (auditFocus_erases (liftWGObserver_erases RxNapi.scheduled_erases))
      (pinned_const _private.Leanux.Proofs.WG.Queues.HolderNapi.«0».Leanux.Proofs.WG.Queues.RxCredits.HolderNapi.scheduled_store)
  · exact softirq

end Leanux.Proofs.WG.RetirementSecurity.HolderNapiKeys
