import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueueSource

/-! A queued ownership cut with the actual source path that reaches it.
The same ledger/debts are kept while the unpublished local is consumed by
the native queue write. An ID-only queued event is not treated as a snapshot. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation

inductive QueuedPath (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (w : World) (history : List CausalJournal.Event)
    (v : World) : List CausalJournal.Event → Prop where
  | installed (peer : Peer) (u : World) (readHistory writes : List CausalJournal.Event)
      (initial : Accounted history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
      (read : runPrefix (QueueHandoff.focused (QueueHandoff.before pid items)) w history =
        (.ok (some peer,u),readHistory))
      (beforeWrite : Accounted readHistory ledger debts (⟨.unpublished,pid,items⟩ :: locals) u.wg)
      (written : runPrefix (QueueHandoff.focused (QueueHandoff.install pid peer items)) u readHistory =
        (.ok ((),v),(readHistory ++ writes) ++ [CausalJournal.txEvent (.queued pid items)]))
      (afterWrite : Accounted ((readHistory ++ writes) ++ [CausalJournal.txEvent (.queued pid items)])
        ledger debts locals v.wg) :
      QueuedPath ledger debts locals pid items w history v
        ((readHistory ++ writes) ++ [CausalJournal.txEvent (.queued pid items)])

/-- The actual install prefix, from the given enqueue caller entry, returns
the very world and history that own the queued batch. -/
theorem QueuedPath.run (path : QueuedPath ledger debts locals pid items w history v last) :
    runPrefix (queueInstallPrefix pid items) w history = (.ok (true,v),last) := by
  cases path with
  | installed peer u readHistory writes initial read beforeWrite written afterWrite =>
    simp only [queueInstallPrefix,runPrefix_bind,read,written,runPrefix_pure]

theorem QueuedPath.accounted (path : QueuedPath ledger debts locals pid items w history v last) :
    Accounted last ledger debts locals v.wg := by
  cases path with
  | installed _ _ _ _ _ _ _ _ afterWrite => exact afterWrite

theorem QueuedPath.event (path : QueuedPath ledger debts locals pid items w history v last) :
    ∃ beforeEvent, last = beforeEvent ++ [CausalJournal.txEvent (.queued pid items)] := by
  cases path with
  | installed _ _ readHistory writes => exact ⟨readHistory ++ writes,rfl⟩

/-- Actual successful installation provides the reached cut without assuming
that the later ring tail or enclosing create operation returns. -/
theorem queue_installed
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (performed : runPrefix (queueInstallPrefix pid items) w history = (.ok (true,v),last)) :
    QueuedPath ledger debts locals pid items w history v last := by
  unfold queueInstallPrefix at performed
  rw [runPrefix_bind] at performed
  cases read : runPrefix (QueueHandoff.focused (QueueHandoff.before pid items)) w history with
  | mk outcome readHistory =>
    rw [read] at performed
    cases outcome with
    | error stop => cases performed
    | ok out =>
      obtain ⟨candidate,u⟩ := out
      cases candidate with
      | none => cases performed
      | some peer =>
        obtain ⟨atRead,cached⟩ := Queue.before_entry pid items before.entry read
        have completeRead := CompleteSource.focused_complete (QueueHandoff.before pid items) w before.complete
        rw [read] at completeRead
        obtain ⟨d,device,found⟩ := cached peer rfl
        obtain ⟨cut,writes,written,atWrite⟩ := Queue.install_entry pid peer items device found atRead
        have completeWrite := CompleteSource.focused_complete (QueueHandoff.install pid peer items) u completeRead
        rw [written] at completeWrite
        dsimp only at performed
        rw [runPrefix_bind,written] at performed
        simp only [runPrefix_pure,Prod.mk.injEq,Except.ok.injEq] at performed
        obtain ⟨⟨_,rfl⟩,rfl⟩ := performed
        exact .installed peer u readHistory writes before read ⟨atRead,completeRead⟩ written ⟨atWrite,completeWrite⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
