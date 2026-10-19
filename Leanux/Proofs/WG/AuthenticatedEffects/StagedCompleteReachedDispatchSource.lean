import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSyscallFrames

/-! A dispatch entry is selected by its numeric position in the original
trace, then reached through the fixed initialized prefix and syscall guard.
The original continuation is retained on both normal and failed runs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CompleteRunner

def callAt (state : RunnerOperation.State) (op : Operation) : Syscall :=
  toSyscall state.2.1 state.2.2.1 state.2.1.size op

structure DispatchPath (trace : Trace) (placeholders : Bool) (count : Nat)
    (op : Operation) (state : RunnerOperation.State) (world : World)
    (history : List CausalJournal.Event) where
  position : trace.ops.toList[count]? = some op
  prior : List CausalJournal.Event
  completed : runPrefixOuter (operationPrefix trace placeholders count) []=(.ok state,prior)
  entered : runPrefix (SyscallSource.enter (callAt state op))
    (RunnerOperation.prepare trace state) prior=(.ok ((),world),history)

def dispatchRemainder (trace : Trace) (count : Nat) (op : Operation)
    (state : RunnerOperation.State) (world : World) :
    PrefixOuter CausalJournal.Event (Lean.Json×World) := do
  let (ret,returned) ← runAtPrefix state.2.1.size world
    (SyscallSource.afterEntry (callAt state op))
  let step ← RunnerOperation.afterCall op state ret returned
  match step with
  | .done final => RunnerOperation.finishWith (fun result w=>(result,w)) trace final
  | .yield final => operationRemainder trace (count+1) final

theorem position_drop (ops : List Operation) (count : Nat) (op : Operation)
    (position : ops[count]?=some op) :
    ops.drop count=op::ops.drop (count+1) := by
  induction ops generalizing count with
  | nil => simp at position
  | cons head rest ih =>
    cases count with
    | zero => simpa using position
    | succ count => exact ih count position

theorem runAt_bind (index : Nat) (w : World) (front : PrefixM E α)
    (tail : α→PrefixM E β) :
    runAtPrefix index w (front >>= tail) = (do
      let (value,v) ← runAtPrefix index w front
      runAtPrefix index v (tail value)) := by
  funext history
  change runPrefixOuter (runAtPrefix index w (front >>= tail)) history =
    runPrefixOuter (do
      let (value,v) ← runAtPrefix index w front
      runAtPrefix index v (tail value)) history
  simp only [runAtPrefix_run,runPrefixOuter_bind,runPrefix_bind]
  cases runPrefix front w history with
  | mk result h => cases result <;> rfl

/-- This equality follows the selected original operation and its fixed
entry guard. It does not infer provenance from an arbitrary factorization. -/
theorem DispatchPath.original
    (path : DispatchPath trace placeholders count op state world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved CausalJournal.hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (dispatchRemainder trace count op state world) history := by
  rw [original_after_prefix trace placeholders count path.completed]
  unfold operationRemainder
  rw [position_drop _ _ _ path.position,List.forIn_cons,bind_assoc]
  unfold RunnerOperation.operation
  rw [bind_assoc,SyscallSource.syscall_factor,runAt_bind,bind_assoc]
  rw [runPrefixOuter_bind,runAtPrefix_run]
  have entered := path.entered
  unfold callAt at entered
  rw [entered]
  simp only [Except.mapError]
  unfold dispatchRemainder
  apply congrArg (fun body : PrefixOuter CausalJournal.Event (Lean.Json×World)=>
    runPrefixOuter body history)
  congr 1
  funext out
  rcases out with ⟨ret,returned⟩
  congr 1
  funext step
  cases step <;> rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
