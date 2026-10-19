import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompletePassive
import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteReleaseFrames

/-! Completion's rekey helper repays its own actual strict borrow. Its
nonfinal receipt is retained and proved terminal-quiet; it is never discarded
merely because the helper does not introduce packet births. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete
open HandshakeSecurity.StagedDisposal LifetimeEffects Fresh CompletionCuts

theorem repayment_complete (pid : PeerId) (complete : Complete history ledger)
    (funded : StagedEntry.Queued.Funded pid w.wg) :
    Complete (runPrefix (liftWGObserver (CausalJournal.completionLifetime.put (some pid))) w history).2 ledger := by
  obtain ⟨g,a,native⟩ := Publication.release_cut_nonfinal pid funded w.ambient
  obtain ⟨suffix,grown,_⟩ := PeerRelease.cut_birth_quiet (some pid) w.wg w.ambient history
  have erased := PeerRelease.cut_erases (some pid) w.wg w.ambient history
  have cutRun : runWGPrefix (PeerRelease.cut (some pid)) w.wg w.ambient history =
      (.ok ((none,g),a),history ++ suffix) := Prod.ext (erased.trans native) grown
  have paired := StagedTerminalComplete.Source.cut_complete (some pid) w.wg w.ambient complete
  rw [cutRun] at paired
  rw [put_actual,PeerRelease.after_cut (some pid) cutRun]
  change Complete ((history ++ suffix) ++ [PeerRelease.receipt (some pid) none w.wg g w.ambient a]) ledger
  apply paired.append_quiet
  intro event member
  cases List.mem_singleton.mp member
  exact release_none_quiet rfl

theorem append_complete (pid : PeerId) (complete : Complete history ledger) (w : World) :
    Complete (runPrefix (liftWGObserver (CausalJournal.completionLifetime.append pid)) w history).2 ledger := by
  exact state_prefix_complete (native := modifyDev fun d => {d with sendWorkQueue := d.sendWorkQueue ++ [pid]})
    (prefix_appends.append pid) (prefix_projects.append pid) complete w

theorem queued_complete (pid : PeerId) (before : Owned context phase history ledger debts w)
    (complete : Complete history ledger) :
    Complete (runPrefix (liftWGObserver (queuedWith CausalJournal.completionLifetime pid false)) w history).2 ledger := by
  have paired := state_prefix_complete (decision_appends pid) (decision_original pid) complete w
  rw [Fresh.queued_factor,liftWGObserver_bind,runPrefix_bind]
  cases run : runPrefix (liftWGObserver (decisionWith CausalJournal.completionLifetime pid)) w history with
  | mk result middle =>
    rw [run] at paired
    cases result with
    | error reason => exact paired
    | ok out =>
      obtain ⟨decision,v⟩ := out
      obtain ⟨native,kept,_⟩ := prefix_returned (decision_appends pid) (decision_original pid)
        (StagedEntry.Queued.decision_views pid) before run
      cases decision with
      | none => exact paired
      | some decision =>
        have funded := decision_funded pid native
        cases decision with
        | true => exact repayment_complete pid paired funded
        | false =>
          simp only [suffixWith,liftWGObserver_bind,runPrefix_bind]
          have installedComplete := state_prefix_complete (install_appends pid) (install_original pid) paired v
          cases installed : runPrefix (liftWGObserver (installWith CausalJournal.completionLifetime pid)) v middle with
          | mk result tail =>
            rw [installed] at installedComplete
            cases result with
            | error reason => exact installedComplete
            | ok out =>
              obtain ⟨ignored,u⟩ := out
              cases ignored
              exact append_complete pid installedComplete u

theorem fresh_complete (pid : PeerId) (before : Owned context phase history ledger debts w)
    (complete : Complete history ledger) :
    Complete (runPrefix (CausalJournal.completionOps.fresh pid) w history).2 ledger := by
  change Complete (runPrefix (liftWGObserver (freshWith CausalJournal.completionLifetime pid)) w history).2 ledger
  have paired := state_prefix_complete (guard_appends pid) (guard_original pid) complete w
  rw [Fresh.fresh_factor,liftWGObserver_bind,runPrefix_bind]
  cases run : runPrefix (liftWGObserver (guardWith CausalJournal.completionLifetime pid)) w history with
  | mk result middle =>
    rw [run] at paired
    cases result with
    | error reason => exact paired
    | ok out =>
      obtain ⟨send,v⟩ := out
      obtain ⟨_,kept,_⟩ := prefix_returned (guard_appends pid) (guard_original pid) (guard_views pid) before run
      cases send
      · exact paired
      · exact queued_complete pid kept paired

theorem sending_fresh (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) :
    Ensures (Sending context initial original remaining) (SendingStopped context initial original)
      (CausalJournal.completionOps.fresh context.pid) (fun _ => Sending context initial original remaining) := by
  intro w history before
  obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before
  obtain ⟨suffix,grown,result⟩ := indexed_fresh_checked context (.sending remaining) ledger debts w history owned
  have paired := fresh_complete context.pid owned complete
  refine ⟨suffix,grown,?_⟩
  cases run : (runPrefix (CausalJournal.completionOps.fresh context.pid) w history).1 with
  | error reason => exact ⟨ledger,debts,trace,(by simpa only [run] using result),paired⟩
  | ok out => exact ⟨ledger,debts,trace,(by simpa only [run] using result),localDebts,paired⟩

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CompletionBatch.Converse
