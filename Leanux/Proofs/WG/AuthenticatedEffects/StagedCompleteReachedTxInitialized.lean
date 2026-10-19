import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIterationInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxActivationCuts

/-! The original initialized schedule and TX activation reach this worker
entry. The crypt-ahead prefix returns its actual state; the packet account
and matched failure classifier are derived from that same reached state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

structure TxEntry (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (pid : PeerId) (world : World) (history : List Event) where
  activation : Activation
  iterationWorld : World
  iterationHistory : List Event
  iteration : Iteration trace placeholders operationIndex activation iterationWorld iterationHistory
  worker : activation.worker=.txWorker
  peer : activation.pid=some pid
  reached : runPrefix (TxActivation.entryPrefix pid) iterationWorld iterationHistory=
    (.ok ((),world),history)

theorem TxEntry.path (entry : TxEntry trace placeholders operationIndex pid world history) :
    ∃ ledger, TxActivation.EntryPath pid entry.iterationWorld entry.iterationHistory ledger world history :=
  TxActivation.entry_path pid entry.iteration.carrier entry.reached

theorem TxEntry.carrier (entry : TxEntry trace placeholders operationIndex pid world history) :
    CompleteProduct.Carrier history world := by
  obtain ⟨_,path⟩ := entry.path
  exact path.carrier

theorem TxEntry.accounted (entry : TxEntry trace placeholders operationIndex pid world history) :
    ∃ ledger, CompleteConsequences.Cut history ledger [] [] world.wg := by
  obtain ⟨ledger,path⟩ := entry.path
  exact ⟨ledger,CompleteConsequences.accounted path.accounted⟩

theorem TxEntry.original (entry : TxEntry trace placeholders operationIndex pid world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (AfterXmit.resume trace operationIndex entry.iteration.entry.caller.path.op
        entry.iteration.entry.caller.path.state entry.iteration.entry.caller.path.ret world
        (TxActivation.tail pid >>= entry.iteration.next)) history := by
  rw [entry.iteration.original]
  apply AfterXmit.resume_run_eq
  rw [TxActivation.iteration_factor entry.activation pid entry.worker entry.peer,
    bind_assoc,runPrefix_bind,entry.reached]

theorem TxEntry.worker_failed (entry : TxEntry trace placeholders operationIndex pid world history)
    (failed : runPrefix (CausalJournal.transmit pid) world history=(.error reason,last)) :
    ∃ ledger, CompleteCarrier.Accounted history ledger [] [] world.wg ∧
      WorkerCompletion.WorkerStop ledger [] pid world history reason last := by
  obtain ⟨ledger,path⟩ := entry.path
  exact ⟨ledger,path.accounted,(WorkerCompletion.worker_failed pid path.accounted failed).2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledRun
