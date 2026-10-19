import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueuePath

/-! Stopped admission retains either its original pre-install failure or
the exact installed queue cut and failed original ring tail. No stopped
World is invented, and no history-only account replaces the source interval. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation

inductive QueueStop (ledger : Ledger) (debts : List CleanupDebt) (locals : List TxLocalBatch)
    (pid : PeerId) (items : List SkbId) (w : World) (history : List CausalJournal.Event)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  | beforeWrite
      (initial : Accounted history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
      (failed : runPrefix (QueueHandoff.focused (QueueHandoff.before pid items)) w history =
        (.error reason,last))
  | afterWrite (cut : World) (cutHistory : List CausalJournal.Event)
      (path : QueuedPath ledger debts locals pid items w history cut cutHistory)
      (failed : runPrefix (QueueHandoff.focused (QueueHandoff.after items)) cut cutHistory =
        (.error reason,last))

theorem queue_stop_of_frontier
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (frontier : Queue.EnqueueFrontier ledger debts locals pid items w history reason last) :
    QueueStop ledger debts locals pid items w history reason last := by
  cases frontier with
  | beforeStopped _ failed => exact .beforeWrite before failed
  | queuedStopped peer u v readHistory writes read written atWrite failed =>
    obtain ⟨atRead,_⟩ := Queue.before_entry pid items before.entry read
    have completeRead := CompleteSource.focused_complete (QueueHandoff.before pid items) w before.complete
    rw [read] at completeRead
    have completeWrite := CompleteSource.focused_complete (QueueHandoff.install pid peer items) u completeRead
    rw [written] at completeWrite
    exact .afterWrite v ((readHistory ++ writes) ++ [CausalJournal.txEvent (.queued pid items)])
      (.installed peer u readHistory writes before read ⟨atRead,completeRead⟩ written ⟨atWrite,completeWrite⟩) failed

theorem QueueStop.run (stopped : QueueStop ledger debts locals pid items w history reason last) :
    runPrefix (Admission.actualOps.enqueue pid items) w history = (.error reason,last) := by
  cases stopped with
  | beforeWrite _ failed =>
    rw [QueueHandoff.actual_enqueue]
    simp only [QueueHandoff.enqueueFocused,runPrefix_bind,failed]
  | afterWrite _ _ path failed =>
    rw [queue_install_factor,runPrefix_bind,path.run]
    dsimp only
    rw [queue_installed_tail,runPrefix_bind,failed]

/-- Every actual enqueue Stop has the original frontier and its exact
publication interval on the same ledger. This is conditional only on the
accounted enqueue entry, not on a completed enclosing caller. -/
theorem queue_stopped_cut (pid : PeerId) (items : List SkbId)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩ :: locals) w.wg)
    (failed : runPrefix (Admission.actualOps.enqueue pid items) w history = (.error reason,last)) :
    Queue.EnqueueFrontier ledger debts locals pid items w history reason last ∧
      QueueStop ledger debts locals pid items w history reason last := by
  have original := Queue.enqueue_cases pid items before.entry
  rw [failed] at original
  exact ⟨original,queue_stop_of_frontier before original⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
