import Leanux.Proofs.WG.RetirementSecurity.HolderDecryptKeys

/-! Native RX/NAPI accounting joins the same scheduler cut as TX and
handshake work. Session support is extracted from the actual owner history;
the decrypt-ring physical witness comes from the existing scheduler carrier. -/
namespace Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Queues.RxCredits

theorem poll_support (entry : Inv initial loans before temporary locals active h w) :
    HolderPoll.Support (Origins.HistorySupport.sessions h) locals active w.wg :=
  ⟨entry.2.2.1,entry.1.2.1.current.2.1,entry.2.2.2.1,entry.2.2.2.2⟩

theorem napi_entry (entry : Inv initial loans before temporary locals active h w) :
    HolderNapiKeys.Inv (Origins.HistorySupport.sessions h) locals active temporary initial loans before h w :=
  ⟨entry.1.1.1,entry.2.1,poll_support entry⟩

theorem softirq : PrefixPreserves (Inv initial loans before temporary locals active)
    OwnerChecks.Safe RxHistory.napiSoftirq := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HolderAuxScheduler.softirq_preserves initial loans before w h entry.1
  have after := (HolderNapiKeys.softirq w h (napi_entry entry)).choose_spec.2.2
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix RxHistory.napiSoftirq w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post after
    exact ⟨post,after.2.1,after.2.2.1,after.2.2.2.2.1,after.2.2.2.2.2⟩

theorem decrypt : PrefixPreserves (Inv initial loans before temporary locals active)
    OwnerChecks.Safe RxHistory.decryptIteration := by
  intro w h entry
  obtain ⟨suffix,history,safe,post⟩ := HolderAuxScheduler.decrypt_preserves initial loans before w h entry.1
  refine ⟨suffix,history,safe,?_⟩
  cases run:(runPrefix RxHistory.decryptIteration w h).1 with
  | error e=>trivial
  | ok out=>
    rw [run] at post
    have after := HolderDecryptKeys.iteration_normal (napi_entry entry) entry.1.1.2 (Prod.ext run rfl)
    exact ⟨post,after.2.1,after.2.2.1,after.2.2.2.2.1,after.2.2.2.2.2⟩

end Leanux.Proofs.WG.RetirementSecurity.HolderScheduled
