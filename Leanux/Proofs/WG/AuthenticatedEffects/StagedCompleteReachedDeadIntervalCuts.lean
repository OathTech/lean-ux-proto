import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadIntervalPath

/-! Splitting one actual ordered path preserves its single final ledger.
Every cut is reached by the fixed list prefix, and its original remaining
list executes to that same completed loop result. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeadIntervals
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation

theorem Path.split
    (path : Path reason pid debts locals count items w history ledger v last after)
    (n : Nat) (bound : n ≤ count) :
    ∃ u middle next,
      Path reason pid debts locals n items w history ledger u middle next ∧
      Path reason pid debts locals (count - n) (items.drop n) u middle next v last after := by
  induction n generalizing count items w history ledger with
  | zero =>
    exact ⟨w,history,ledger,.nil path.entry.1 path.entry.2,by simpa only [Nat.sub_zero,List.drop_zero] using path⟩
  | succ n ih =>
    cases path with
    | nil before pending => omega
    | cons first rest =>
      obtain ⟨u,middle,next,leading,suffix⟩ := ih rest (by omega)
      exact ⟨u,middle,next,.cons first leading,
        by simpa only [List.drop_succ_cons,Nat.add_sub_add_right] using suffix⟩

/-- Every loop boundary is a native cut of the same original run. Earlier
terminals and remaining backed pending tickets refer to the same ledger;
the suffix reaches the one fixed completed result, not a fresh witness. -/
theorem Path.interval
    (path : Path reason pid debts locals items.length items w history ledger v last after)
    (n : Nat) (bound : n ≤ items.length) :
    ∃ u middle next,
      Path reason pid debts locals n items w history ledger u middle next ∧
      Path reason pid debts locals (items.length - n) (items.drop n) u middle next v last after ∧
      runPrefix (loop reason (items.take n)) w history = (.ok ((),u),middle) ∧
      runPrefix (loop reason (items.drop n)) u middle = (.ok ((),v),last) ∧
      Staged.Obligations.Step ledger next ∧ Staged.Obligations.Step next after ∧
      Accounted middle next debts (⟨.selected,pid,items.drop n⟩ :: locals) u.wg ∧
      PendingBatch middle next (items.drop n) ∧ AllDropped middle next reason (items.take n) := by
  obtain ⟨u,middle,next,leading,suffix⟩ := path.split n bound
  refine ⟨u,middle,next,leading,suffix,leading.run,?_,leading.result.1,suffix.result.1,
    leading.result.2.1,leading.result.2.2,leading.dropped⟩
  have exactRun := suffix.run
  simpa only [←List.length_drop,List.take_length] using exactRun

theorem completed_intervals (reason : Terminal.Reason) (items : List SkbId)
    (before : Accounted history ledger debts (⟨.selected,pid,items⟩ :: locals) w.wg)
    (pending : PendingBatch history ledger items) :
    ∃ v last after,
      Path reason pid debts locals items.length items w history ledger v last after ∧
      runPrefix (loop reason items) w history = (.ok ((),v),last) ∧
      Accounted last after debts locals v.wg ∧
      ∀ n, n ≤ items.length → ∃ u middle next,
        Path reason pid debts locals n items w history ledger u middle next ∧
        Path reason pid debts locals (items.length - n) (items.drop n) u middle next v last after ∧
        runPrefix (loop reason (items.take n)) w history = (.ok ((),u),middle) ∧
        runPrefix (loop reason (items.drop n)) u middle = (.ok ((),v),last) ∧
        Staged.Obligations.Step ledger next ∧ Staged.Obligations.Step next after ∧
        Accounted middle next debts (⟨.selected,pid,items.drop n⟩ :: locals) u.wg ∧
        PendingBatch middle next (items.drop n) ∧ AllDropped middle next reason (items.take n) := by
  obtain ⟨v,last,after,path⟩ := total reason items before pending
  have final : Accounted last after debts (⟨.selected,pid,[]⟩ :: locals) v.wg := by
    simpa only [List.drop_length] using path.result.2.1
  exact ⟨v,last,after,path,by simpa only [List.take_length] using path.run,
    ⟨empty_local .selected final.entry,final.complete⟩,fun n bound => path.interval n bound⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DeadIntervals
