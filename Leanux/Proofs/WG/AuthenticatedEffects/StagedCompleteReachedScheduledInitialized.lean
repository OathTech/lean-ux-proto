import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAfterXmitContext

/-! A scheduler entry reached through the initialized post-transmit crypt
branch. Its caller contains only original operation and source-run evidence;
the native account is derived, rather than an incoming assumption. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

structure Entry (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (world : World) (history : List Event) where
  callerWorld : World
  callerHistory : List Event
  caller : AfterXmit.Caller trace placeholders operationIndex callerWorld callerHistory
  reached : runPrefix AfterXmit.front callerWorld callerHistory=(.ok (some true,world),history)

theorem Entry.carrier (entry : Entry trace placeholders operationIndex world history) :
    CompleteProduct.Carrier history world :=
  (entry.caller.schedule_entry entry.reached).1

theorem Entry.original (entry : Entry trace placeholders operationIndex world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (AfterXmit.resume trace operationIndex entry.caller.path.op
        entry.caller.path.state entry.caller.path.ret world
        (Driver.scheduleObserved hooks none >>= fun _=>AfterXmit.afterScheduled)) history :=
  entry.caller.schedule_continuation entry.reached

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ScheduledRun
