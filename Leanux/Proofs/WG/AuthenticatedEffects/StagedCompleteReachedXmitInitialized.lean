import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedXmitCaller
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDispatchEntry

/-! The routed transmit entry comes from the selected syscall of the original
initialized runner. Its native prefix and remaining FD/fixture cleanup are
retained even when a later part of that same execution stops. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

structure Caller (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (world : World) (history : List Event) where
  op : Operation
  state : RunnerOperation.State
  dispatch : DispatchPath trace placeholders operationIndex op state world history
  family : Nat
  addr : Nat
  payload : List UInt8
  opts : Env.XmitOpts
  selected : callAt state op=.wgXmit family addr payload opts

def resume (trace : Trace) (operationIndex : Nat) (op : Operation)
    (state : RunnerOperation.State) (world : World) (body : PrefixM Event Int) :
    PrefixOuter Event (Lean.Json×World) := do
  let (ret,returned) ← runAtPrefix state.2.1.size world do
    let ret ← body
    SyscallSource.afterDispatch (callAt state op) ret
  let step ← RunnerOperation.afterCall op state ret returned
  match step with
  | .done final => RunnerOperation.finishWith (fun result w=>(result,w)) trace final
  | .yield final => operationRemainder trace (operationIndex+1) final

theorem Caller.entry (caller : Caller trace placeholders operationIndex world history) :
    CompleteProduct.Carrier history world := caller.dispatch.entry.1.1

theorem Caller.original (caller : Caller trace placeholders operationIndex world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (resume trace operationIndex caller.op caller.state world
        (Driver.syscallXmitObserved hooks caller.family caller.addr caller.payload caller.opts)) history := by
  rw [caller.dispatch.original]
  unfold dispatchRemainder SyscallSource.afterEntry resume
  rw [caller.selected]
  rfl

theorem Caller.transmit_entry (caller : Caller trace placeholders operationIndex world history)
    (path : Path caller.family caller.addr caller.payload caller.opts history world
      fd acquired packets mtu worldAt) :
    CompleteProduct.Carrier (entryHistory caller.family caller.addr packets mtu history) worldAt :=
  path.entry caller.entry

theorem Caller.transmit_cut (caller : Caller trace placeholders operationIndex world history)
    (path : Path caller.family caller.addr caller.payload caller.opts history world
      fd acquired packets mtu worldAt) :
    ∃ ledger, CompleteConsequences.Cut
      (entryHistory caller.family caller.addr packets mtu history) ledger [] [] worldAt.wg := by
  obtain ⟨ledger,account⟩ := path.accounted caller.entry
  exact ⟨ledger,CompleteConsequences.accounted account⟩

theorem Caller.transmit_continuation (caller : Caller trace placeholders operationIndex world history)
    (path : Path caller.family caller.addr caller.payload caller.opts history world
      fd acquired packets mtu worldAt) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (resume trace operationIndex caller.op caller.state worldAt
        (callTail caller.family caller.addr caller.payload
          (.transmit fd packets mtu history.length)))
        (entryHistory caller.family caller.addr packets mtu history) := by
  rw [caller.original]
  unfold resume
  rw [whole_factor,bind_assoc,runAt_bind,bind_assoc,runPrefixOuter_bind,runAtPrefix_run,path.literal]
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Xmit
