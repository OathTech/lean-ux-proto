import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerSource

/-! The initialized prefix is a literal take/drop split of the original
operation loop. Its native entry witness is not an arbitrary factorization
chosen to obtain a desired state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CompleteRunner

theorem loop_append (call : Syscall→PrefixM E Int) (trace : Trace)
    (front rest : List Operation) (state : RunnerOperation.State) :
    forIn (front++rest) state (RunnerOperation.operation call trace) =
      (forIn front state (RunnerOperation.operation call trace) >>= fun middle=>
        forIn rest middle (RunnerOperation.operation call trace)) := by
  funext history
  change runPrefixOuter _ history=runPrefixOuter _ history
  induction front generalizing state history with
  | nil=>simp only [List.nil_append,List.forIn_nil,runPrefixOuter_bind,runPrefixOuter_pure]
  | cons op ops ih=>
    simp only [List.cons_append,List.forIn_cons,runPrefixOuter_bind]
    cases performed : runPrefixOuter (RunnerOperation.operation call trace op state) history with
    | mk result h=>
      cases result with
      | error reason=>rfl
      | ok step=>
        obtain ⟨middle,same,_⟩ := RunnerOperation.operation_index call trace op state performed
        subst step
        simpa only [runPrefixOuter_bind] using ih middle h

def operationRemainder (trace : Trace) (count : Nat) (state : RunnerOperation.State) :
    PrefixOuter CausalJournal.Event (Lean.Json×World) := do
  let final ← forIn (trace.ops.toList.drop count) state
    (RunnerOperation.operation (Driver.syscallObserved CausalJournal.hooks) trace)
  RunnerOperation.finishWith (fun result w=>(result,w)) trace final

/-- The same actual prefill, boot, accumulator and operation list are kept
on both sides. The remainder still contains the original final guards. -/
theorem initialized_factor (trace : Trace) (placeholders : Bool) (count : Nat) :
    RoutingJoint.executeTraceWith (Driver.syscallObserved CausalJournal.hooks)
      (fun result w=>(result,w)) trace placeholders =
      (operationPrefix trace placeholders count >>= operationRemainder trace count) := by
  change ConservationRunner.prefillWith trace.seccompPrefill
    (ConservationRunner.fixture trace placeholders) (fun w=>
      ConservationRunner.bootWith trace.net trace.foreign w
        (RoutingJoint.runnerTailWith (Driver.syscallObserved CausalJournal.hooks)
          (fun result w=>(result,w)) trace)) = _
  unfold operationPrefix
  conv => lhs; rw [prefill_factor]
  conv => rhs; rw [prefill_factor,bind_assoc]
  congr 1
  funext w
  conv => lhs; rw [boot_factor]
  conv => rhs; rw [boot_factor,bind_assoc]
  congr 1
  funext v
  rw [RunnerOperation.tail_factor,←Array.forIn_toList]
  have splitLoop := loop_append (Driver.syscallObserved CausalJournal.hooks) trace
    (trace.ops.toList.take count) (trace.ops.toList.drop count) (v,#[],#[],#[],#[],#[])
  rw [List.take_append_drop] at splitLoop
  rw [splitLoop,bind_assoc]
  rfl

theorem original_after_prefix (trace : Trace) (placeholders : Bool) (count : Nat)
    (prior : runPrefixOuter (operationPrefix trace placeholders count) []=(.ok state,history)) :
    runPrefixOuter (RoutingJoint.executeTraceWith (Driver.syscallObserved CausalJournal.hooks)
      (fun result w=>(result,w)) trace placeholders) [] =
      runPrefixOuter (operationRemainder trace count state) history := by
  rw [initialized_factor trace placeholders count,runPrefixOuter_bind,prior]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RunnerSource
