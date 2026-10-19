import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDeadIntervalCuts

/-! All DEAD iteration boundaries are tied to the original worker selection.
No completed outer worker is required: after the total original free loop,
the original repayment continuation may return or Stop. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open TransmitSecurity.Staged.Obligations StagedTerminalComplete CompleteCarrier
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedConservation

def workerDeadFreePrefix (pid : PeerId) (n : Nat) : PrefixM CausalJournal.Event Unit := do
  let selected ← workerSelection pid
  match selected with
  | none => pure ()
  | some picked =>
    if picked.crypted then pure ()
    else loop (.deadBatch pid picked.head) (picked.items.take n)

theorem SelectionPath.dead_free_prefix_run
    (path : SelectionPath ledger locals pid w history ⟨items,head,false⟩ u middle)
    (performed : runPrefix (loop (.deadBatch pid head) (items.take n)) u middle = (.ok ((),v),last)) :
    runPrefix (workerDeadFreePrefix pid n) w history = (.ok ((),v),last) := by
  rw [workerDeadFreePrefix,runPrefix_bind,path.run]
  exact performed

theorem SelectionPath.dead_cleanup_continuation
    (path : SelectionPath ledger locals pid w history ⟨items,head,false⟩ u middle)
    (performed : runPrefix (loop (.deadBatch pid head) items) u middle = (.ok ((),v),last)) :
    runPrefix (CausalJournal.transmit pid) w history = runPrefix (DeadEntry.repay pid head.keypair) v last := by
  rw [path.callback_run]
  change runPrefix (Terminal.deadObserved CausalJournal.txEvent CausalJournal.txEvent?
    CausalJournal.Event.stagedDisposal CausalJournal.Event.terminalDrop pid items head) u middle = _
  rw [DeadEntry.dead_factor,runPrefix_bind,performed]

/-- Every ordered DEAD-loop prefix reaches its actual cut from the fixed
worker entry. All cuts share one completed loop result and its original
repayment continuation; their remaining selected cells and terminal tickets
are accounted on the exact successor of the same incoming ledger. -/
theorem SelectionPath.dead_cleanup_intervals
    (path : SelectionPath ledger locals pid w history ⟨items,head,false⟩ u middle) :
    ∃ v last after,
      DeadIntervals.Path (.deadBatch pid head) pid [] locals items.length items u middle ledger v last after ∧
      Accounted last after [] locals v.wg ∧
      runPrefix (CausalJournal.transmit pid) w history = runPrefix (DeadEntry.repay pid head.keypair) v last ∧
      ∀ n, n ≤ items.length → ∃ cutWorld cutHistory next,
        runPrefix (workerDeadFreePrefix pid n) w history = (.ok ((),cutWorld),cutHistory) ∧
        runPrefix (loop (.deadBatch pid head) (items.drop n)) cutWorld cutHistory = (.ok ((),v),last) ∧
        DeadIntervals.Path (.deadBatch pid head) pid [] locals n items u middle ledger cutWorld cutHistory next ∧
        DeadIntervals.Path (.deadBatch pid head) pid [] locals (items.length - n) (items.drop n)
          cutWorld cutHistory next v last after ∧
        Staged.Obligations.Step ledger next ∧ Staged.Obligations.Step next after ∧
        Accounted cutHistory next [] (⟨.selected,pid,items.drop n⟩ :: locals) cutWorld.wg ∧
        PendingBatch cutHistory next (items.drop n) ∧
        AllDropped cutHistory next (.deadBatch pid head) (items.take n) := by
  obtain ⟨v,last,after,full,performed,accounted,cuts⟩ :=
    DeadIntervals.completed_intervals (.deadBatch pid head) items path.accounted_entry.1 path.accounted_entry.2
  refine ⟨v,last,after,full,accounted,path.dead_cleanup_continuation performed,?_⟩
  intro n bound
  obtain ⟨cutWorld,cutHistory,next,leading,suffix,entered,finished,step,steps,atCut,pending,dropped⟩ := cuts n bound
  exact ⟨cutWorld,cutHistory,next,path.dead_free_prefix_run entered,finished,leading,suffix,
    step,steps,atCut,pending,dropped⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached
