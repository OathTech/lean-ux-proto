import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedScheduleCaller
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxActivationCuts

/-! TX-worker entry from either initialized scheduler caller. Crypt-ahead
finishes at the actual source state before the selected completion worker;
its exact accounting and original continuation are derived from that path. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
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
  reached : runPrefix (TxActivation.entryPrefix pid) iterationWorld iterationHistory=(.ok ((),world),history)

def TxEntry.resume (entry : TxEntry trace placeholders operationIndex pid world history)
    (w : World) (body : PrefixM Event Bool) : PrefixOuter Event (Lean.Json×World) :=
  entry.iteration.resume w (body >>= TxActivation.continuation)

theorem TxEntry.carrier (entry : TxEntry trace placeholders operationIndex pid world history) :
    CompleteProduct.Carrier history world :=
  Scheduler.checked_normal (TxActivation.entry_checked pid) entry.iteration.carrier entry.reached

theorem TxEntry.original (entry : TxEntry trace placeholders operationIndex pid world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume world (CausalJournal.transmit pid)) history := by
  rw [entry.iteration.original]
  apply entry.iteration.resume_run_eq
  rw [TxActivation.iteration_factor entry.activation pid entry.worker entry.peer,
    runPrefix_bind,entry.reached]
  rfl

theorem TxEntry.resume_run_eq (entry : TxEntry trace placeholders operationIndex pid world history)
    (left right : PrefixM Event Bool) (same : runPrefix left w before=runPrefix right v after) :
    runPrefixOuter (entry.resume w left) before=runPrefixOuter (entry.resume v right) after :=
  entry.iteration.resume_run_eq _ _ (Scheduler.bind_run_equal TxActivation.continuation same)

theorem TxEntry.accounted (entry : TxEntry trace placeholders operationIndex pid world history) :
    ∃ ledger, CompleteConsequences.Cut history ledger [] [] world.wg := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  exact ⟨ledger,CompleteConsequences.accounted before⟩

theorem TxEntry.worker_failed (entry : TxEntry trace placeholders operationIndex pid world history)
    (failed : runPrefix (CausalJournal.transmit pid) world history=(.error reason,last)) :
    ∃ ledger, CompleteCarrier.Accounted history ledger [] [] world.wg ∧
      WorkerCompletion.WorkerStop ledger [] pid world history reason last := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  exact ⟨ledger,before,(WorkerCompletion.worker_failed pid before failed).2⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
