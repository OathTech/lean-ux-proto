import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchEntry

/-! The original dispatch return carries the same initialized packet account
into the return-to-user callbacks. A negative syscall result is still a
normal native return; Stop supplies no fabricated world. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CompleteRunner CausalJournal
variable {state : RunnerOperation.State} {returned : World}

theorem dispatch_checked (call : Syscall) :
    CompletePrefix.Ensures CompleteRunner.DeleteFrames.Entry CompleteProduct.Safe
      (Driver.dispatchObserved hooks call) (fun _=>CompleteProduct.Carrier) := by
  by_cases deletion : call=.wgDelete
  · subst call
    exact CompletePrefix.Runner.Delete.dispatch
  · exact (CompletePrefix.Product.Outer.dispatch_except_delete call deletion).consequence
      (fun _ _ before=>before.1) (fun _ _ _ after=>after)

theorem DispatchPath.dispatch_return
    (path : DispatchPath trace placeholders count op state world history)
    (performed : runPrefix (Driver.dispatchObserved hooks (callAt state op)) world history=
      (.ok (ret,returned),last)) :
    CompletePrefix.With CompleteProduct.Carrier CompleteProduct.Safe last returned := by
  obtain ⟨_,_,_,after⟩ := dispatch_checked (callAt state op) world history path.entry
  simpa only [performed] using after

def returnRemainder (trace : Trace) (count : Nat) (op : Operation)
    (state : RunnerOperation.State) (ret : Int) (world : World) :
    PrefixOuter Event (Lean.Json×World) := do
  let (value,returned) ← runAtPrefix state.2.1.size world
    (SyscallSource.afterDispatch (callAt state op) ret)
  let step ← RunnerOperation.afterCall op state value returned
  match step with
  | .done final => RunnerOperation.finishWith (fun result w=>(result,w)) trace final
  | .yield final => operationRemainder trace (count+1) final

theorem DispatchPath.original_after_dispatch
    (path : DispatchPath trace placeholders count op state world history)
    (performed : runPrefix (Driver.dispatchObserved hooks (callAt state op)) world history=
      (.ok (ret,returned),last)) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (returnRemainder trace count op state ret returned) last := by
  rw [path.original]
  unfold dispatchRemainder SyscallSource.afterEntry
  rw [runAt_bind,bind_assoc,runPrefixOuter_bind,runAtPrefix_run,performed]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
