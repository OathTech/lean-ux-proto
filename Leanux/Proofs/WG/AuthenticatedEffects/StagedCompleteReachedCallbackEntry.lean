import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedReturnPath

/-! The callback is selected at its original numeric position, after an
actual initialized dispatch and literal return-callback prefix. The fixed
remaining callback list and runner continuation accompany that entry. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CallbackSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

structure Entry (trace : Trace) (placeholders : Bool) (operationIndex callbackIndex : Nat)
    (body : PrefixM Event Unit) (world : World) (history : List Event) where
  path : CallbackPath trace placeholders operationIndex callbackIndex world history
  selected : (ReturnSource.callbacks (callAt path.state path.op))[callbackIndex]?=some body

theorem selected_drop (items : List α) (count : Nat) (value : α)
    (selected : items[count]?=some value) : items.drop count=value::items.drop (count+1) := by
  induction items generalizing count with
  | nil => simp at selected
  | cons head rest ih =>
    cases count with
    | zero => simpa using selected
    | succ count => exact ih count selected

def Entry.resume (entry : Entry trace placeholders operationIndex callbackIndex body world history)
    (w : World) (action : PrefixM Event Unit) : PrefixOuter Event (Lean.Json×World) := do
  let (ret,returned) ← runAtPrefix entry.path.state.2.1.size w do
    action
    ReturnSource.sequence ((ReturnSource.callbacks (callAt entry.path.state entry.path.op)).drop (callbackIndex+1))
    ReturnSource.routing (callAt entry.path.state entry.path.op)
    pure entry.path.ret
  let step ← RunnerOperation.afterCall entry.path.op entry.path.state ret returned
  match step with
  | .done final => RunnerOperation.finishWith (fun result w=>(result,w)) trace final
  | .yield final => operationRemainder trace (operationIndex+1) final

theorem Entry.carrier (entry : Entry trace placeholders operationIndex callbackIndex body world history) :
    CompleteProduct.Carrier history world := entry.path.entry.1

theorem Entry.original (entry : Entry trace placeholders operationIndex callbackIndex body world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume world body) history := by
  rw [entry.path.original]
  unfold callbackRemainder ReturnSource.callbackSuffix Entry.resume
  rw [selected_drop _ _ _ entry.selected]
  simp only [ReturnSource.sequence,bind_assoc]
  rfl

/-- This transports a source-path equality through the fixed callback
context. Its premise alone is not a native reachability certificate. -/
theorem Entry.resume_run_eq
    (entry : Entry trace placeholders operationIndex callbackIndex body world history)
    (left right : PrefixM Event Unit)
    (same : runPrefix left w before=runPrefix right v after) :
    runPrefixOuter (entry.resume w left) before=runPrefixOuter (entry.resume v right) after := by
  unfold Entry.resume
  simp only [runAt_bind,bind_assoc,runPrefixOuter_bind,runAtPrefix_run]
  rw [same]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CallbackSource
