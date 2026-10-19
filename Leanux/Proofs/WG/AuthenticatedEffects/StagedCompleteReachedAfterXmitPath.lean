import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAfterXmitFrames

/-! The post-transmit worker entry is connected to the original initialized
wgXmit operation and its first return callback, with the native guard and
optional crypt branch retained. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity RunnerSource

structure Caller (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (world : World) (history : List CausalJournal.Event) where
  path : CallbackPath trace placeholders operationIndex 0 world history
  family : Nat
  addr : Nat
  payload : List UInt8
  opts : Env.XmitOpts
  selected : callAt path.state path.op=.wgXmit family addr payload opts

def resume (trace : Trace) (operationIndex : Nat) (op : Operation)
    (state : RunnerOperation.State) (ret : Int) (world : World)
    (body : PrefixM CausalJournal.Event Unit) : PrefixOuter CausalJournal.Event (Lean.Json×World) := do
  let (value,returned) ← runAtPrefix state.2.1.size world do
    body
    Driver.idleTimersObserved CausalJournal.hooks
    pure ret
  let step ← RunnerOperation.afterCall op state value returned
  match step with
  | .done final => RunnerOperation.finishWith (fun result w=>(result,w)) trace final
  | .yield final => operationRemainder trace (operationIndex+1) final

theorem Caller.original (caller : Caller trace placeholders operationIndex world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved CausalJournal.hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (resume trace operationIndex caller.path.op caller.path.state caller.path.ret
        world (Driver.afterXmitObserved CausalJournal.hooks)) history := by
  rw [caller.path.original]
  unfold callbackRemainder ReturnSource.callbackSuffix
  rw [caller.selected]
  simp only [ReturnSource.callbacks,List.drop_zero,ReturnSource.sequence,ReturnSource.routing,
    bind_assoc,pure_bind]
  rfl

theorem Caller.front_entry (caller : Caller trace placeholders operationIndex world history)
    (performed : runPrefix front world history=(.ok (choice,v),last)) :
    CompletePrefix.With CompleteProduct.Carrier CompleteProduct.Safe last v := by
  obtain ⟨_,_,_,after⟩ := front_checked world history caller.path.entry
  simpa only [performed] using after

theorem Caller.front_continuation (caller : Caller trace placeholders operationIndex world history)
    (performed : runPrefix front world history=(.ok (choice,v),last)) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved CausalJournal.hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (resume trace operationIndex caller.path.op caller.path.state caller.path.ret
        v (tail choice)) last := by
  rw [caller.original]
  unfold resume
  rw [front_factor,bind_assoc,runAt_bind,bind_assoc,runPrefixOuter_bind,runAtPrefix_run,performed]
  rfl

theorem Caller.send_entry (caller : Caller trace placeholders operationIndex world history)
    (performed : runPrefix sendPrefix world history=(.ok (true,v),last)) :
    CompletePrefix.With CompleteProduct.Carrier CompleteProduct.Safe last v := by
  obtain ⟨_,_,_,after⟩ := send_prefix_checked world history caller.path.entry
  simpa only [performed] using after

theorem Caller.send_continuation (caller : Caller trace placeholders operationIndex world history)
    (performed : runPrefix sendPrefix world history=(.ok (true,v),last)) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved CausalJournal.hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (resume trace operationIndex caller.path.op caller.path.state caller.path.ret
        v (Driver.sendWorkersObserved CausalJournal.hooks)) last := by
  rw [caller.original]
  unfold resume
  rw [send_factor,bind_assoc,runAt_bind,bind_assoc,runPrefixOuter_bind,runAtPrefix_run,performed]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.AfterXmit
