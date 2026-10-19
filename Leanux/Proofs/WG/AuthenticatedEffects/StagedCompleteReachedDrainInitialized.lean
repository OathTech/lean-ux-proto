import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendDrainCuts

/-! The original callback and post-transmit send drains retain their exact
bounded-loop worker entry and initialized continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

structure WorkerEntry (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (world : World) (history : List Event) where
  callerWorld : World
  callerHistory : List Event
  caller : Entry trace placeholders operationIndex callerWorld callerHistory
  path : SendDrain.WorkerPath callerWorld callerHistory world history

theorem WorkerEntry.carrier (entry : WorkerEntry trace placeholders operationIndex world history) :
    CompleteProduct.Carrier history world := entry.path.carrier entry.caller.carrier

theorem WorkerEntry.original (entry : WorkerEntry trace placeholders operationIndex world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.caller.resume world (do
        Driver.sendWorkerObserved hooks
        Driver.scheduleObserved hooks none
        SendDrain.remaining entry.path.rest)) history := by
  rw [entry.caller.original]
  exact entry.caller.resume_run_eq _ _ entry.path.continuation

theorem WorkerEntry.accounted (entry : WorkerEntry trace placeholders operationIndex world history) :
    ∃ ledger, CompleteConsequences.Cut history ledger [] [] world.wg := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  exact ⟨ledger,CompleteConsequences.accounted before⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendRun
