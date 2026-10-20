import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRunnerPointSource

/-! Canonical witnesses select only original runner branches and list positions.
The indexed original action remains unchanged; this file defines no evaluator. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
open Lean Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal

inductive Callback where
  | sends | idle | afterXmit | advance | route | cleanup

def Callback.action : Callback → PrefixM Event Unit
  | .sends => Driver.sendWorkersObserved hooks
  | .idle => Driver.idleTimersObserved hooks
  | .afterXmit => Driver.afterXmitObserved hooks
  | .advance => Driver.afterAdvanceObserved hooks
  | .route => liftPrefix Env.routeIntoWg0
  | .cleanup => liftPrefix Env.netnsCleanup

def callbacks : Syscall → List Callback
  | .wgSet _ | .wgInject .. => [.sends,.idle]
  | .wgUp => [.sends,.idle,.route]
  | .wgXmit .. => [.afterXmit,.idle]
  | .wgBatch .. => [.idle]
  | .wgAdvance .. => [.advance]
  | .wgNetnsClose => [.cleanup]
  | _ => []

theorem callbacks_source (call : Syscall) : (callbacks call).map Callback.action=ReturnSource.callbacks call := by
  cases call <;> rfl

noncomputable def callbackShape (callback : Callback) (index : Nat) (w : World) :
    Shape (runAtPrefix index w callback.action) := by
  cases callback with
  | sends => exact .child index w .sends
  | idle => exact .child index w .idle
  | afterXmit => exact .child index w .afterXmit
  | advance => exact .child index w .advance
  | route => exact .native (.stored index w PrefixStore.routeShape)
  | cleanup => exact .native (.cleanup index w)

noncomputable def sequenceShape (call : Syscall) (actions : List Callback)
    (offset index : Nat) (w : World) :
    Shape (runAtPrefix index w (ReturnSource.sequence (actions.map Callback.action))) := by
  induction actions generalizing offset w with
  | nil => rw [List.map_nil,ReturnSource.sequence,runAt_pure]; exact .pure _
  | cons action rest ih =>
    rw [List.map_cons,ReturnSource.sequence,runAt_bind]
    exact .bind (.marked (.callback call offset) w (callbackShape action index w))
      (fun out => ih (offset+1) out.2)

noncomputable def afterDispatchShape (call : Syscall) (ret : Int) (index : Nat) (w : World) :
    Shape (runAtPrefix index w (SyscallSource.afterDispatch call ret)) := by
  rw [ReturnSource.after_dispatch_factor,runAt_bind]
  apply Shape.bind (.native (.stored index w PrefixStore.preludeShape))
  intro out
  rw [runAt_bind]
  rw [←callbacks_source call]
  apply Shape.bind (sequenceShape call (callbacks call) 0 index out.2)
  intro after
  rw [runAt_bind]
  apply Shape.bind (.native (.stored index after.2 (PrefixStore.routingShape call)))
  intro final
  rw [runAt_pure]
  exact .pure _

noncomputable def syscallShape (call : Syscall) (index : Nat) (w : World) :
    Shape (runAtPrefix index w (Driver.syscallObserved hooks call)) := by
  rw [SyscallSource.syscall_factor,runAt_bind]
  apply Shape.bind (.native (.stored index w (PrefixStore.enterShape call)))
  intro entered
  unfold SyscallSource.afterEntry
  rw [runAt_bind]
  exact .bind (.child index entered.2 (.dispatch call))
    (fun out => afterDispatchShape call out.1 index out.2)

noncomputable def afterCallShape (op : Operation) (state : State) (ret : Int) (w : World) :
    Shape (RunnerOperation.afterCall (E:=Event) op state ret w) := by
  apply Shape.marked (.afterCall state.2.1.size op) w
  unfold RunnerOperation.afterCall
  apply Shape.bind (.native (.stored state.2.1.size w PrefixStore.skipShape))
  intro out
  rcases out with ⟨ignored,v⟩
  apply Shape.marked (.metadata state.2.1.size) v
  cases hidden : v.ambient.hidden with
  | none =>
    all_goals cases suspended : v.ambient.suspended
    all_goals cases pending : v.ambient.pendingWork
    all_goals cases raised : v.wg.netRxRaised
    all_goals simp only [hidden,suspended,pending,raised]
    all_goals repeat' first
      | (exact .pure _)
      | (exact .stopped _)
      | (apply Shape.bind)
      | (apply arrayShape)
      | (intro)
      | (simp +failIfUnchanged only)
  | some records =>
    cases records
    all_goals cases suspended : v.ambient.suspended
    all_goals cases pending : v.ambient.pendingWork
    all_goals cases raised : v.wg.netRxRaised
    all_goals simp only [hidden,suspended,pending,raised]
    all_goals repeat' first
      | (exact .pure _)
      | (exact .stopped _)
      | (apply Shape.bind)
      | (apply arrayShape)
      | (intro)
      | (simp +failIfUnchanged only)

noncomputable def operationShape (trace : Trace) (op : Operation) (state : State) :
    Shape (RunnerOperation.operation (Driver.syscallObserved hooks) trace op state) := by
  apply Shape.marked (.operation state.2.1.size op) state.1
  unfold RunnerOperation.operation
  apply Shape.bind (.marked (.prepared state.2.1.size op) (RunnerOperation.prepare trace state)
    (syscallShape _ _ _))
  intro out
  exact afterCallShape op state out.1 out.2

noncomputable def finishShape (trace : Trace) (state : State) :
    Shape (RunnerOperation.finishWith (E:=Event) (fun j w=>(j,w)) trace state) := by
  apply Shape.marked .finish state.1
  unfold RunnerOperation.finishWith
  repeat' first
    | (exact .pure _)
    | (exact .stopped _)
    | (apply Shape.bind)
    | (intro)
    | (simp +failIfUnchanged only)
    | split

noncomputable def tailShape (trace : Trace) (w : World) :
    Shape (RoutingJoint.runnerTailWith (Driver.syscallObserved hooks) (fun j w=>(j,w)) trace w) := by
  rw [RunnerOperation.tail_factor,←Array.forIn_toList]
  exact .bind (listShape trace.ops.toList (w,#[],#[],#[],#[],#[]) _ (operationShape trace))
    (finishShape trace)

noncomputable def executeShape (trace : Trace) (placeholders : Bool) :
    Shape (RoutingJoint.executeTraceWith (Driver.syscallObserved hooks) (fun j w=>(j,w)) trace placeholders) := by
  apply Shape.marked .fixture (ConservationRunner.fixture trace placeholders)
  change Shape (ConservationRunner.prefillWith trace.seccompPrefill
    (ConservationRunner.fixture trace placeholders) (fun w=>
      ConservationRunner.bootWith trace.net trace.foreign w
        (RoutingJoint.runnerTailWith (Driver.syscallObserved hooks) (fun j w=>(j,w)) trace)))
  rw [CompleteRunner.prefill_factor]
  apply Shape.bind (.native (.prefill trace.seccompPrefill (ConservationRunner.fixture trace placeholders)))
  intro w
  rw [CompleteRunner.boot_factor]
  exact .bind (.native (.boot trace.net trace.foreign w)) (tailShape trace)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Runner.Points
