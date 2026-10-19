import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueueInteriorWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionInitialized

/-! The initialized TX entry supplies the one fixed ledger, and its original
selection supplies the actual cached cohort. Native dequeue and its pending
observations preserve that ledger and the initialized runner continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
open QueueInterior RetirementSecurity

theorem TxEntry.dequeue_interval
    (entry : TxEntry trace placeholders operationIndex pid world history)
    (selected : runPrefix (workerSelection pid) world history=(.ok (some picked,v),last)) :
    ∃ ledger u middle d p,
      runPrefix (headPrefix pid) world history=(.ok (some (picked.items,picked.head),u),middle) ∧
      u.wg.dev=some d ∧ d.peers[pid]?=some p ∧ p.txQueue.peeked=some picked.items ∧
      let after := replacePeer u.wg d pid {p with txQueue:=p.txQueue.dropPeeked}
      let reads := middle++[readEvent pid p,readEvent pid p]
      runPrefix (workerMutation pid) world history=(.ok (some (p,p),{u with wg:=after}),reads) ∧
      CompleteConsequences.Cut reads ledger [] [⟨.selected,pid,picked.items⟩] after ∧
      AllocatedObligation.CreateDisposal.PendingBatch reads ledger picked.items ∧
      p.txQueue.all=picked.items::p.txQueue.dropPeeked.all ∧
      CompleteConsequences.Cut (reads++[writeEvent pid p]) ledger [] [⟨.selected,pid,picked.items⟩] after ∧
      CompleteConsequences.Cut (reads++[writeEvent pid p,removedEvent pid picked.items]) ledger []
        [⟨.selected,pid,picked.items⟩] after ∧
      runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
        (fun result w=>(result,w)) trace placeholders) [] =
        runPrefixOuter (entry.resume {u with wg:=after} (do
          dropDue pid picked.items (p,p)
          afterDrop pid picked.items picked.head)) reads := by
  obtain ⟨ledger,path⟩ := entry.selected selected
  obtain ⟨u,middle,d,p,head,before,device,resident,cached⟩ := selection_head path
  obtain ⟨_,pending,cohort,shape,_⟩ := drop_pending before device resident cached
  obtain ⟨written,recorded⟩ := drop_recorded before device resident cached
  refine ⟨ledger,u,middle,d,p,head,device,resident,cached,
    worker_mutation_run head device resident,CompleteConsequences.accounted pending,cohort,shape,
    CompleteConsequences.accounted written,CompleteConsequences.accounted recorded,?_⟩
  rw [entry.original]
  apply entry.resume_run_eq
  exact worker_continuation head device resident

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
