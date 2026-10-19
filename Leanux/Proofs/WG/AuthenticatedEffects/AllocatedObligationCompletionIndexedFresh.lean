import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionFreshGuard
import Leanux.Proofs.WG.AuthenticatedEffects.CausalCallbackQuiet

/-! The actual rekey callback uses its own borrowed reference and preserves
the same indexed entry. A stopped call retains the real callback entry and
its exact failed prefix; no terminal release is silently framed away. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity
open HandshakeSecurity.StagedDisposal TransmitSecurity.Staged.Obligations LifetimeEffects CompletionCuts

theorem put_appends (peer : Option PeerId) : StateAppends (CausalJournal.completionLifetime.put peer) := by
  exact (CausalJournal.CallbackQuiet.peer (fun _ => (none : Option Unit)) _ _
    (fun _ => rfl) (fun _ => rfl) peer).1

theorem queued_appends (pid : PeerId) : StateAppends (queuedWith CausalJournal.completionLifetime pid false) := by
  rw [queued_factor]
  apply StateAppends.bind (decision_appends pid)
  intro decision
  cases decision with
  | none => exact StateAppends.pure _
  | some value =>
    cases value with
    | true => exact put_appends _
    | false =>
      apply StateAppends.bind (install_appends pid)
      intro ignored
      exact prefix_appends.append pid

theorem fresh_appends (pid : PeerId) : StateAppends (freshWith CausalJournal.completionLifetime pid) := by
  rw [fresh_factor]
  apply StateAppends.bind (guard_appends pid)
  intro send
  cases send
  · exact StateAppends.pure _
  · exact queued_appends pid

theorem fresh_checked (pid : PeerId) (before : Owned context phase history ledger debts w) :
    match runPrefix (liftWGObserver (freshWith CausalJournal.completionLifetime pid)) w history with
    | (.error _,last) => last.filterMap ledgerEvent? = history.filterMap ledgerEvent?
    | (.ok (_,v),last) => Owned context phase last ledger debts v := by
  rw [fresh_factor,liftWGObserver_bind,runPrefix_bind]
  cases run : runPrefix (liftWGObserver (guardWith CausalJournal.completionLifetime pid)) w history with
  | mk result middle =>
    cases result with
    | error reason => exact prefix_failed (guard_original pid) run
    | ok out =>
      obtain ⟨send,v⟩ := out
      obtain ⟨_,kept,quiet⟩ := prefix_returned (guard_appends pid) (guard_original pid)
        (guard_views pid) before run
      cases send
      · exact kept
      · have checked := queued_checked pid kept
        dsimp only
        simp only [ite_true]
        cases result : runPrefix (liftWGObserver (queuedWith CausalJournal.completionLifetime pid false)) v middle with
        | mk outcome last =>
          cases outcome with
          | error reason =>
            have same : last.filterMap ledgerEvent? = middle.filterMap ledgerEvent? := by
              simpa only [result] using checked
            exact same.trans quiet
          | ok out => simpa only [result] using checked

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Fresh

namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations CompletionCuts

theorem indexed_fresh_checked (context : Context) (phase : Phase) (ledger : Ledger)
    (debts : List CleanupDebt) :
    Ensures (fun h w => Owned context phase h ledger debts w) (IndexedStopped context ledger debts)
      (CausalJournal.completionOps.fresh context.pid)
      (fun _ h w => Owned context phase h ledger debts w) := by
  intro w history before
  have checked := Fresh.fresh_checked context.pid before
  change (match runPrefix (CausalJournal.completionOps.fresh context.pid) w history with
    | (.error _,last) => last.filterMap ledgerEvent? = history.filterMap ledgerEvent?
    | (.ok (_,v),last) => Owned context phase last ledger debts v) at checked
  obtain ⟨suffix,grown⟩ := (Fresh.fresh_appends context.pid).liftWGObserver w history
  change (runPrefix (CausalJournal.completionOps.fresh context.pid) w history).2 = history ++ suffix at grown
  refine ⟨suffix,grown,?_⟩
  cases run : runPrefix (CausalJournal.completionOps.fresh context.pid) w history with
  | mk result last =>
    cases result with
    | ok out => simpa only [run] using checked
    | error reason =>
      rw [run] at checked
      dsimp only at checked
      have extended : last = history ++ suffix := by simpa only [run] using grown
      refine ⟨⟨phase,.fresh context.pid,w,history,before,⟨suffix,extended.symm⟩,run,checked,?_⟩⟩
      rw [extended]
      apply births_quiet_suffix
      have empty : suffix.filterMap ledgerEvent? = [] := by
        rw [extended,List.filterMap_append] at checked
        exact List.append_cancel_left (as := history.filterMap ledgerEvent?)
          (by simpa only [List.append_nil] using checked)
      exact fun event member => ledger_quiet_birth event (List.filterMap_eq_nil_iff.mp empty event member)

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch
