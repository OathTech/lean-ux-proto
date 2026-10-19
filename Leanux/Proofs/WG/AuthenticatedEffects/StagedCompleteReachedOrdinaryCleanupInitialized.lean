import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedOrdinaryCleanupWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSelectionInitialized

/-! Initialization supplies the selected worker account. Successful scoped
sending derives its one terminal ledger and ordinary cleanup path; every
native erase is then reached by the original worker and runner continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource
open AllocatedObligation CompletionBatch

theorem TxEntry.cleanup_interiors
    (entry : TxEntry trace placeholders operationIndex pid world history)
    (selected : runPrefix (workerSelection pid) world history=(.ok (some ⟨items,head,true⟩,u),middle))
    (completed : runPrefix (CompletionEffects.completeScoped Event.scope
      CausalSources.Cause.completion completionOps pid items) u middle=(.ok ((),freeWorld),freeHistory)) :
    ∃ initial, ∃ context : CompletionBatch.Context, context.pid=pid ∧ context.locals=[] ∧ context.items=items ∧
      context.initialLedger=initial ∧
      ∃ ledger debts final last,
        SendSettlements context initial [] ledger debts ∧
        CleanupPath context ledger items debts freeWorld freeHistory final last ∧
        ∀ done skb rest, items=done++skb::rest →
          ∃ cutWorld cutHistory cutDebts generation nextWorld,
            OrdinaryCleanup.Interval context ledger cutDebts skb rest cutWorld cutHistory generation nextWorld ∧
            ∀ phase : CleanupPrimitive.Phase,
              runPrefix (OrdinaryCleanup.workerPrefix pid done skb phase) world history=
                (.ok ((),nextWorld),CleanupPrimitive.current phase cutWorld skb cutHistory) ∧
              CompleteConsequences.Cut (CleanupPrimitive.current phase cutWorld skb cutHistory) ledger
                (forgetFreedCell cutHistory generation skb cutDebts)
                (⟨.selected,context.pid,rest⟩ :: context.locals) nextWorld.wg ∧
              runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
                (fun result w=>(result,w)) trace placeholders) [] =
                runPrefixOuter (entry.resume nextWorld (do
                  OrdinaryCleanup.due phase cutWorld skb
                  freeLoop cleanupOps rest
                  CompletionBatch.release cleanupOps pid head.keypair))
                  (CleanupPrimitive.current phase cutWorld skb cutHistory) := by
  obtain ⟨initial,path⟩ := entry.selected selected
  obtain ⟨context,peer,locals,batch,origin,ledger,debts,final,last,settlements,cleaned⟩ :=
    OrdinaryCleanup.selected_cleanup_path path completed
  refine ⟨initial,context,peer,locals,batch,origin,ledger,debts,final,last,settlements,cleaned,?_⟩
  intro done skb rest shape
  have splitPath : CleanupPath context ledger (done++skb::rest) debts freeWorld freeHistory final last := shape ▸ cleaned
  obtain ⟨cutWorld,cutHistory,cutDebts,generation,nextWorld,leading,interval,_⟩ :=
    OrdinaryCleanup.prefix_interval done splitPath
  refine ⟨cutWorld,cutHistory,cutDebts,generation,nextWorld,interval,?_⟩
  intro phase
  refine ⟨OrdinaryCleanup.worker_prefix_run path completed (OrdinaryCleanup.prefix_run leading interval phase),
    CompleteConsequences.accounted (interval.accounted phase),?_⟩
  rw [entry.original]
  apply entry.resume_run_eq
  exact OrdinaryCleanup.worker_continuation path completed shape leading interval phase

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledSource
