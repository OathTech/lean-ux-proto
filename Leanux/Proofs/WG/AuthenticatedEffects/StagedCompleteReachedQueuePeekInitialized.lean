import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueuePeekObserved
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedScheduleTxEntry

/-! The actual initialized worker entry supplies the one ledger for its
native peek setter. Original clock and read events are retained through the
one pending write event and unchanged worker-body continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
open QueueInterior RetirementSecurity AllocatedObligation

theorem TxEntry.peek_interval
    (entry : TxEntry trace placeholders operationIndex pid world history)
    (device : world.wg.dev=some d) (resident : d.peers[pid]?=some p)
    (chosen : ((p.txQueue.peek).run world.wg).run world.ambient=.ok (((first,queue),world.wg),b)) :
    ∃ ledger,
      let after := replacePeer world.wg d pid {p with txQueue:=queue}
      let reads := history++[readEvent pid p,readEvent pid p]
      runPrefix (peekMutation pid) world history=(.ok ((first,p),{world with wg:=after,ambient:=b}),reads) ∧
      CompleteConsequences.Cut reads ledger [] [] after ∧
      (∀ items, first=some items → CreateDisposal.PendingBatch reads ledger items) ∧
      queue.all=p.txQueue.all ∧ queue.peeked=first ∧
      runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
        (fun result w=>(result,w)) trace placeholders) [] =
        runPrefixOuter (entry.resume {world with wg:=after,ambient:=b}
          (peekDue pid (first,p) >>= TxWorker.body pid)) reads := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  obtain ⟨reached,account,pending,contents,cached,remaining⟩ := peek_pending before device resident chosen
  refine ⟨ledger,reached,CompleteConsequences.accounted account,pending,contents,cached,?_⟩
  rw [entry.original]
  apply entry.resume_run_eq
  rw [TxWorker.transmit_factor,runPrefix_bind,remaining,runPrefix_bind]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
