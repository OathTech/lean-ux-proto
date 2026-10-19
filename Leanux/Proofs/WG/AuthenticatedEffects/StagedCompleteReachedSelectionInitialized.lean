import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionReturned
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedScheduleTxEntry

/-! The initialized scheduler supplies the worker's entry account, while
the original successful selection supplies its exact chosen batch. No later
callback failure or incoming selected ownership is needed. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

theorem TxEntry.selected
    (entry : TxEntry trace placeholders operationIndex pid world history)
    (performed : runPrefix (workerSelection pid) world history=(.ok (some picked,v),last)) :
    ∃ ledger, SelectionPath ledger [] pid world history picked v last := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  exact ⟨ledger,selection_returned before performed⟩

theorem TxEntry.selected_accounted
    (entry : TxEntry trace placeholders operationIndex pid world history)
    (performed : runPrefix (workerSelection pid) world history=(.ok (some picked,v),last)) :
    ∃ ledger, CompleteConsequences.Cut last ledger [] [⟨.selected,pid,picked.items⟩] v.wg ∧
      AllocatedObligation.CreateDisposal.PendingBatch last ledger picked.items := by
  obtain ⟨ledger,path⟩ := entry.selected performed
  exact ⟨ledger,CompleteConsequences.accounted path.accounted_entry.1,path.accounted_entry.2⟩

theorem TxEntry.selected_continuation
    (entry : TxEntry trace placeholders operationIndex pid world history)
    (performed : runPrefix (workerSelection pid) world history=(.ok (some picked,v),last)) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume v (selectedCallback pid (some picked))) last := by
  rw [entry.original]
  apply entry.resume_run_eq
  rw [worker_selection_factor,runPrefix_bind,performed]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
