import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReturnFrames

/-! Initialized return callback cuts use the original operation, actual
dispatch return and literal ordered callback prefix. Their native accounts
and continuations are derived on that same path. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CompleteRunner

structure CallbackPath (trace : Trace) (placeholders : Bool)
    (operationIndex callbackIndex : Nat) (world : World) (history : List CausalJournal.Event) where
  op : Operation
  state : RunnerOperation.State
  dispatchWorld : World
  dispatchHistory : List CausalJournal.Event
  dispatch : DispatchPath trace placeholders operationIndex op state dispatchWorld dispatchHistory
  ret : Int
  returnWorld : World
  returnHistory : List CausalJournal.Event
  dispatchRun : runPrefix (Driver.dispatchObserved CausalJournal.hooks (callAt state op))
    dispatchWorld dispatchHistory=(.ok (ret,returnWorld),returnHistory)
  callbackRun : runPrefix (ReturnSource.callbackPrefix (callAt state op) callbackIndex)
    returnWorld returnHistory=(.ok ((),world),history)

def callbackRemainder (trace : Trace) (operationIndex callbackIndex : Nat)
    (op : Operation) (state : RunnerOperation.State) (ret : Int) (world : World) :
    PrefixOuter CausalJournal.Event (Lean.Json×World) := do
  let (value,returned) ← runAtPrefix state.2.1.size world
    (ReturnSource.callbackSuffix (callAt state op) callbackIndex ret)
  let step ← RunnerOperation.afterCall op state value returned
  match step with
  | .done final => RunnerOperation.finishWith (fun result w=>(result,w)) trace final
  | .yield final => operationRemainder trace (operationIndex+1) final

theorem CallbackPath.entry
    (path : CallbackPath trace placeholders operationIndex callbackIndex world history) :
    CompletePrefix.With CompleteProduct.Carrier CompleteProduct.Safe history world := by
  have before := path.dispatch.dispatch_return path.dispatchRun
  obtain ⟨_,_,_,after⟩ := ReturnSource.prefix_checked (callAt path.state path.op) callbackIndex
    path.returnWorld path.returnHistory before
  simpa only [path.callbackRun] using after

theorem CallbackPath.cut
    (path : CallbackPath trace placeholders operationIndex callbackIndex world history) :
    ∃ ledger, CompleteConsequences.Cut history ledger [] [] world.wg := by
  obtain ⟨ledger,before⟩ := path.entry.1.1
  exact ⟨ledger,CompleteConsequences.accounted before⟩

/-- Even if the callback or later runner stops, the retained continuation
starts at this exact initialized world and original callback position. -/
theorem CallbackPath.original
    (path : CallbackPath trace placeholders operationIndex callbackIndex world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved CausalJournal.hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (callbackRemainder trace operationIndex callbackIndex path.op path.state
        path.ret world) history := by
  rw [path.dispatch.original_after_dispatch path.dispatchRun]
  unfold returnRemainder
  rw [ReturnSource.callback_factor _ _ callbackIndex,runAt_bind,bind_assoc,
    runPrefixOuter_bind,runAtPrefix_run,path.callbackRun]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
