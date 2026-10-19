import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedScheduleCaller
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedEncryptionEntryAheadPath
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxActivationSource

/-! Initialized encryption iterations reached by the scheduler or by the
original TX crypt-ahead branch. Their selected poll item and callback entry
come from the actual source, with all remaining work still attached. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

inductive Iteration (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (world : World) (history : List Event) : Type where
  | direct {activation}
      (caller : ScheduledSource.Iteration trace placeholders operationIndex activation world history)
      (worker : activation.worker=.encryptWorker)
  | ahead {activation callerWorld callerHistory}
      (caller : ScheduledSource.Iteration trace placeholders operationIndex activation callerWorld callerHistory)
      (pid : PeerId) (enc : Activation)
      (worker : activation.worker=.txWorker) (peer : activation.pid=some pid)
      (performed : runPrefix (EncryptionEntry.aheadPrefix pid) callerWorld callerHistory=
        (.ok (some enc,world),history))

def Iteration.resume (cut : Iteration trace placeholders operationIndex world history)
    (w : World) (body : PrefixM Event IterResult) : PrefixOuter Event (Lean.Json×World) :=
  match cut with
  | .direct caller _ => caller.resume w body
  | .ahead caller pid enc _ _ _ => caller.resume w (do
      let result ← body
      EncryptionEntry.aheadFinish pid enc result
      TxActivation.tail pid)

theorem Iteration.carrier (cut : Iteration trace placeholders operationIndex world history) :
    CompleteProduct.Carrier history world := by
  cases cut with
  | direct caller _ => exact caller.carrier
  | ahead caller pid _ _ _ performed =>
      exact Scheduler.checked_normal (EncryptionEntry.ahead_prefix_checked pid) caller.carrier performed

theorem Iteration.original (cut : Iteration trace placeholders operationIndex world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (cut.resume world (Driver.encryptIterObserved hooks)) history := by
  cases cut with
  | direct caller worker =>
      rw [caller.original]
      apply caller.resume_run_eq
      simp only [Driver.iterationObserved,worker]
  | ahead caller pid enc worker peer performed =>
      rw [caller.original]
      apply caller.resume_run_eq
      rw [TxActivation.iteration_factor _ pid worker peer]
      change runPrefix (Driver.cryptAheadObserved hooks pid >>= fun _=>TxActivation.tail pid) _ _ = _
      rw [EncryptionEntry.ahead_factor,bind_assoc,runPrefix_bind,performed]
      simp only [EncryptionEntry.aheadBranch,bind_assoc]

theorem Iteration.resume_run_eq (cut : Iteration trace placeholders operationIndex world history)
    (left right : PrefixM Event IterResult) (same : runPrefix left w before=runPrefix right v after) :
    runPrefixOuter (cut.resume w left) before=runPrefixOuter (cut.resume v right) after := by
  cases cut with
  | direct caller _ => exact caller.resume_run_eq left right same
  | ahead caller pid enc _ _ _ =>
      apply caller.resume_run_eq
      exact Scheduler.bind_run_equal (fun result=>do
        EncryptionEntry.aheadFinish pid enc result
        TxActivation.tail pid) same

structure Entry (trace : Trace) (placeholders : Bool) (operationIndex : Nat)
    (item : Option (List SkbId)) (world : World) (history : List Event) where
  iterationWorld : World
  iterationHistory : List Event
  iteration : Iteration trace placeholders operationIndex iterationWorld iterationHistory
  reached : runPrefix EncryptionEntry.entryPrefix iterationWorld iterationHistory=(.ok (item,world),history)

def Entry.resume (entry : Entry trace placeholders operationIndex item world history)
    (w : World) (body : PrefixM Event Bool) : PrefixOuter Event (Lean.Json×World) :=
  entry.iteration.resume w (body >>= EncryptionEntry.continuation)

theorem Entry.carrier (entry : Entry trace placeholders operationIndex item world history) :
    CompleteProduct.Carrier history world :=
  Scheduler.checked_normal EncryptionEntry.entry_checked entry.iteration.carrier entry.reached

theorem Entry.original (entry : Entry trace placeholders operationIndex item world history) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (entry.resume world (hooks.encrypt item)) history := by
  rw [entry.iteration.original]
  apply entry.iteration.resume_run_eq
  rw [EncryptionEntry.iteration_factor,runPrefix_bind,entry.reached]
  rfl

theorem Entry.resume_run_eq (entry : Entry trace placeholders operationIndex item world history)
    (left right : PrefixM Event Bool) (same : runPrefix left w before=runPrefix right v after) :
    runPrefixOuter (entry.resume w left) before=runPrefixOuter (entry.resume v right) after :=
  entry.iteration.resume_run_eq _ _ (Scheduler.bind_run_equal EncryptionEntry.continuation same)

theorem Entry.accounted (entry : Entry trace placeholders operationIndex item world history) :
    ∃ ledger, CompleteConsequences.Cut history ledger [] [] world.wg := by
  obtain ⟨ledger,before⟩ := entry.carrier.1
  exact ⟨ledger,CompleteConsequences.accounted before⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.EncryptionRun
