import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCallbackEntry
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAfterXmitContext

/-! The send drain has two initialized return paths: a selected original
callback, or the send suffix of the original post-transmit callback. Both
retain a concrete source path and its actual runner continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

inductive Entry (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (world : World) (history : List Event) : Type where
  | callback {callbackIndex}
      (path : CallbackSource.Entry trace placeholders operationIndex callbackIndex
        (Driver.sendWorkersObserved hooks) world history)
  | afterXmit {callerWorld callerHistory}
      (caller : AfterXmit.Caller trace placeholders operationIndex callerWorld callerHistory)
      (reached : runPrefix AfterXmit.sendPrefix callerWorld callerHistory=(.ok (true,world),history))

def Entry.resume (entry : Entry trace placeholders operationIndex world history)
    (w : World) (body : PrefixM Event Unit) : PrefixOuter Event (Lean.Json×World) :=
  match entry with
  | .callback path => path.resume w body
  | .afterXmit caller _ => AfterXmit.resume trace operationIndex caller.path.op caller.path.state caller.path.ret w body

theorem Entry.carrier (entry : Entry trace placeholders operationIndex world history) :
    CompleteProduct.Carrier history world := by
  cases entry with
  | callback path => exact path.carrier
  | afterXmit caller reached => exact (caller.send_entry reached).1

theorem Entry.original (entry : Entry trace placeholders operationIndex world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume world (Driver.sendWorkersObserved hooks)) history := by
  cases entry with
  | callback path => exact path.original
  | afterXmit caller reached => exact caller.send_continuation reached

theorem Entry.resume_run_eq (entry : Entry trace placeholders operationIndex world history)
    (left right : PrefixM Event Unit) (same : runPrefix left w before=runPrefix right v after) :
    runPrefixOuter (entry.resume w left) before=runPrefixOuter (entry.resume v right) after := by
  cases entry with
  | callback path => exact path.resume_run_eq left right same
  | afterXmit caller _ => exact AfterXmit.resume_run_eq _ _ _ _ _ left right same

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SendRun
