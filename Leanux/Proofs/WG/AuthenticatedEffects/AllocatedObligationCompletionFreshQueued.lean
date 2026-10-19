import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFreshCuts

/-! The queued helper's own borrow discharges its repayment obligation.
Only a failed access prefix can stop: the reached repayment and append arms
are total, and the same explicit completion ledger survives both arms. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedDisposal TransmitSecurity.Staged.Obligations LifetimeEffects

theorem decision_funded (pid : PeerId)
    (native : (liftWG (StagedEntry.Queued.decisionPrefix pid)).run w = .ok (some decision,v)) :
    StagedEntry.Queued.Funded pid v.wg := by
  rw [liftWG_run] at native
  cases run : ((StagedEntry.Queued.decisionPrefix pid).run w.wg).run w.ambient with
  | error reason => simp only [run,Except.map] at native; cases native
  | ok out =>
    obtain ⟨⟨value,g⟩,a⟩ := out
    simp only [run,Except.map,Except.ok.injEq,Prod.mk.injEq] at native
    obtain ⟨rfl,rfl⟩ := native
    exact StagedEntry.Queued.decision_funded pid _ _ run

theorem append_total (pid : PeerId) (before : Owned context phase history ledger debts w) :
    ∃ v last, runPrefix (liftWGObserver (CausalJournal.completionLifetime.append pid)) w history =
      (.ok ((),v),last) ∧ Owned context phase last ledger debts v := by
  obtain ⟨source,_,_⟩ := StagedEntry.Queued.append_total before.entry pid w.ambient
  rw [append_actual]
  refine ⟨{w with wg := StagedEntry.Queued.queuedWorld pid w.wg},history ++
    [.queued ⟨CausalScope.current CausalJournal.scope? history,pid,
      ⟨(),w.wg,StagedEntry.Queued.queuedWorld pid w.wg,w.ambient,w.ambient⟩⟩],?_,?_⟩
  · simp only [liftWGObserver_run,source,Except.map]
  · exact (before.same_view (StagedEntry.Queued.queued_view pid w.wg)).append [_]
      (by intro event member; simp only [List.mem_singleton] at member; subst event; rfl)

theorem queued_checked (pid : PeerId) (before : Owned context phase history ledger debts w) :
    match runPrefix (liftWGObserver (queuedWith CausalJournal.completionLifetime pid false)) w history with
    | (.error _,last) => last.filterMap ledgerEvent? = history.filterMap ledgerEvent?
    | (.ok (_,v),last) => Owned context phase last ledger debts v := by
  rw [queued_factor,liftWGObserver_bind,runPrefix_bind]
  cases run : runPrefix (liftWGObserver (decisionWith CausalJournal.completionLifetime pid)) w history with
  | mk result middle =>
    cases result with
    | error reason => exact prefix_failed (decision_original pid) run
    | ok out =>
      obtain ⟨decision,v⟩ := out
      obtain ⟨native,kept,quiet⟩ := prefix_returned (decision_appends pid) (decision_original pid)
        (StagedEntry.Queued.decision_views pid) before run
      cases decision with
      | none => exact kept
      | some decision =>
        have funded := decision_funded pid native
        cases decision with
        | true =>
          obtain ⟨g,a,suffix,_,paid,after⟩ := repayment_total pid kept funded
          change (match runPrefix (liftWGObserver (CausalJournal.completionLifetime.put (some pid))) v middle with
            | (.error _,last) => last.filterMap ledgerEvent? = history.filterMap ledgerEvent?
            | (.ok (_,after),last) => Owned context phase last ledger debts after)
          rw [paid]
          exact after
        | false =>
          simp only [suffixWith,liftWGObserver_bind,runPrefix_bind]
          cases installed : runPrefix (liftWGObserver (installWith CausalJournal.completionLifetime pid)) v middle with
          | mk result tail =>
            cases result with
            | error reason => exact (prefix_failed (install_original pid) installed).trans quiet
            | ok out =>
              obtain ⟨ignored,u⟩ := out
              cases ignored
              obtain ⟨_,ready,_⟩ := prefix_returned (install_appends pid) (install_original pid)
                (StagedEntry.Queued.install_views pid) kept installed
              obtain ⟨lastWorld,lastHistory,appended,after⟩ := append_total pid ready
              dsimp only
              rw [appended]
              exact after

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
