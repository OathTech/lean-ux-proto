import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxActivationSource

/-! A successful original crypt-ahead prefix chooses the actual TX entry.
The complete ledger and native allocation carrier are obtained at that exact
world and journal, with no callback or independent reachability premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxActivation
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations CompleteCarrier

structure EntryPath (pid : PeerId) (w : World) (history : List CausalJournal.Event)
    (ledger : Ledger) (u : World) (middle : List CausalJournal.Event) : Prop where
  performed : runPrefix (entryPrefix pid) w history = (.ok ((),u),middle)
  extended : ∃ suffix, middle = history ++ suffix
  carrier : CompleteProduct.Carrier middle u
  accounted : Accounted middle ledger [] [] u.wg

theorem entry_path (pid : PeerId) (before : CompleteProduct.Carrier history w)
    (performed : runPrefix (entryPrefix pid) w history = (.ok ((),u),middle)) :
    ∃ ledger, EntryPath pid w history ledger u middle := by
  obtain ⟨suffix,grown,_,kept⟩ := entry_checked pid w history before
  simp only [performed] at grown kept
  obtain ⟨ledger,accounted⟩ := kept.1
  exact ⟨ledger,performed,⟨suffix,grown⟩,kept,accounted⟩

theorem EntryPath.iteration_run
    (path : EntryPath pid w history ledger u middle)
    (activation : Activation) (worker : activation.worker = .txWorker)
    (peer : activation.pid = some pid) :
    runPrefix (Driver.iterationObserved CausalJournal.hooks activation) w history =
      runPrefix (tail pid) u middle := by
  rw [iteration_factor activation pid worker peer,runPrefix_bind,path.performed]

theorem entry_failed (activation : Activation) (pid : PeerId)
    (worker : activation.worker = .txWorker) (peer : activation.pid = some pid)
    (performed : runPrefix (entryPrefix pid) w history = (.error reason,last)) :
    runPrefix (Driver.iterationObserved CausalJournal.hooks activation) w history = (.error reason,last) := by
  rw [iteration_factor activation pid worker peer,runPrefix_bind,performed]

/-- Both alternatives retain an original source run. The stopped prefix
has no invented returned world. In the other alternative the original
transmit-and-reschedule continuation starts at the chosen entry. -/
theorem entry_cases (activation : Activation) (pid : PeerId)
    (worker : activation.worker = .txWorker) (peer : activation.pid = some pid)
    (before : CompleteProduct.Carrier history w) :
    (∃ reason last, runPrefix (entryPrefix pid) w history = (.error reason,last) ∧
      runPrefix (Driver.iterationObserved CausalJournal.hooks activation) w history = (.error reason,last) ∧
      CompleteProduct.Safe last) ∨
    ∃ ledger u middle, EntryPath pid w history ledger u middle ∧
      runPrefix (Driver.iterationObserved CausalJournal.hooks activation) w history =
        runPrefix (tail pid) u middle := by
  cases performed : runPrefix (entryPrefix pid) w history with
  | mk outcome middle =>
    cases outcome with
    | error reason =>
      obtain ⟨_,_,safe,_⟩ := entry_checked pid w history before
      exact Or.inl ⟨reason,middle,rfl,entry_failed activation pid worker peer performed,
        by simpa only [performed] using safe⟩
    | ok out =>
      obtain ⟨value,u⟩ := out
      cases value
      obtain ⟨ledger,path⟩ := entry_path pid before performed
      exact Or.inr ⟨ledger,u,middle,path,path.iteration_run activation worker peer⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxActivation
