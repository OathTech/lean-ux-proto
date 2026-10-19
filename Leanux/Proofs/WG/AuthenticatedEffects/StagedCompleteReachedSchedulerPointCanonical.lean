import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSchedulerPointSource

set_option maxHeartbeats 1000000

/-! Canonical source witnesses. Each value below is constructed from the
literal named scheduler program; callers do not supply a factorization. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity CausalJournal

elab "scheduler_shape_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing source action"
  let .const actual _ := action.consumeMData.headBeta.getAppFn
    | Lean.throwError "not a constant source head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different source head"

elab "scheduler_native_head " expected:ident : tactic => do
  let target := (← Lean.instantiateMVars (← (← Lean.Elab.Tactic.getMainGoal).getType)).consumeMData
  unless target.isAppOf ``Shape do Lean.throwError "not a source shape"
  let some action := target.getAppArgs.back? | Lean.throwError "missing action"
  unless action.consumeMData.isAppOf ``liftPrefix do Lean.throwError "not a native lift"
  let some native := action.getAppArgs.back? | Lean.throwError "missing native action"
  let native := native.consumeMData
  let native ← if native.isAppOf ``liftWG then
      match native.getAppArgs.back? with
      | some action => pure action.consumeMData
      | none => Lean.throwError "missing WG action"
    else pure native
  let .const actual _ := native.getAppFn | Lean.throwError "not a native head"
  let name := expected.getId.eraseMacroScopes.toString
  unless actual.toString == name || actual.toString.endsWith ("." ++ name) do
    Lean.throwError "different native head"

macro "scheduler_shape_step" : tactic => `(tactic|
  first
  | (scheduler_shape_head Pure.pure; exact .pure _)
  | (scheduler_shape_head Bind.bind; apply Shape.bind)
  | (scheduler_native_head getDev; exact .native .device)
  | (scheduler_native_head Env.pendingDevice; exact .native (.pendingDevice _ _))
  | (scheduler_native_head getAmbient; exact .native .ambient)
  | (scheduler_native_head peekHiddenSite; exact .native .hiddenSite)
  | (scheduler_native_head peekUnit; exact .native (.unit _))
  | (scheduler_native_head resolveUnit; exact .native (.resolve _ _ _))
  | (scheduler_native_head modifyDev; exact .native (.eraseWork _))
  | (scheduler_native_head hidden; first | exact .native (.start _) | exact .native (.stop _))
  | (scheduler_native_head modifyAmbient; exact .native (.resume _))
  | (scheduler_native_head pendingNapi; exact .native (.pending _))
  | (scheduler_native_head Env.Activation.hasWork; exact .native (.work _))
  | (scheduler_native_head List.filterM; exact .native (.trials _))
  | (scheduler_native_head invariant; exact .native (.invariant _))
  | (scheduler_native_head unsupported; exact .native (.unsupported _))
  | (scheduler_native_head budgetExhausted; exact .native (.exhausted _))
  | maintenance_intro
  | split
  | (simp +failIfUnchanged only))

noncomputable def runStepShape (occupancy index : Nat) (state : RunState) : Shape (runStep index state) := by
  apply Shape.marked (.runIndex state.2 occupancy index)
  unfold runStep
  apply Shape.bind (.child (.iteration state.2))
  intro result
  cases result with
  | ended => exact .bind (.native (.stop state.2.worker)) (fun _ => .pure _)
  | continued => exact .pure _
  | yielded => exact .bind (.native (.suspend state.2)) (fun _ => .pure _)

noncomputable def runFinishShape (a : Activation) (occupancy refills : Nat) (state : RunState) :
    Shape (runFinish a occupancy refills state) := by
  unfold runFinish
  cases state.1 <;> dsimp only
  · exact .native (.invariant _)
  · exact .pure _

noncomputable def runShape (a : Activation) : Shape (SourceScheduler.run iteration a) := by
  apply Shape.marked (.run a)
  rw [run_factor]
  apply Shape.bind (.native (.occupancy a))
  intro occupancy
  apply Shape.bind (.native .refills)
  intro refills
  rw [runBody_list]
  apply Shape.bind (listShape _ _ _ (runStepShape occupancy))
  exact runFinishShape a occupancy refills

noncomputable def dispatchChooseShape (worker : Worker) : Shape (dispatchChoose worker) := by
  unfold dispatchChoose
  apply Shape.bind (.native .device)
  intro device
  cases worker <;> dsimp only
  all_goals repeat' scheduler_shape_step

noncomputable def dispatchShape (worker : Worker) :
    Shape (SourceScheduler.dispatch iteration worker) := by
  apply Shape.marked (.dispatch worker)
  rw [dispatch_factor]
  apply Shape.bind (dispatchChooseShape worker)
  intro chosen
  cases chosen with
  | none => exact .pure _
  | some a => exact .bind (runShape a) (fun _ => .pure _)

noncomputable def chooseShape (stack : Option Worker) : Shape (choose stack) := by
  apply Shape.marked (.choose stack)
  unfold choose
  repeat' scheduler_shape_step

noncomputable def performShape (chosen : Choice) : Shape (perform chosen) := by
  cases chosen with
  | idle => exact .pure _
  | next => exact .pure _
  | dispatch worker required =>
      unfold perform
      apply Shape.bind (dispatchShape worker)
      intro dispatched
      repeat' scheduler_shape_step
      | napi =>
      unfold perform
      apply Shape.bind (.child .napi)
      intro result
      repeat' scheduler_shape_step
      | resumed a => exact .bind (runShape a) (fun _ => .pure _)

noncomputable def scheduleStepShape (stack : Option Worker) (budget index : Nat) (state : ScheduleState) :
    Shape (scheduleStep stack index state) :=
  .marked (.scheduleIndex stack budget index) (.bind (chooseShape stack) performShape)

noncomputable def scheduleFinishShape (state : ScheduleState) : Shape (scheduleFinish state) := by
  unfold scheduleFinish
  cases state.1 <;> dsimp only
  · exact .native (.exhausted _)
  · exact .pure _

noncomputable def scheduleShape (stack : Option Worker) : Shape (Driver.scheduleObserved hooks stack) := by
  apply Shape.marked (.schedule stack)
  rw [schedule_factor]
  apply Shape.bind (.native .budget)
  intro budget
  rw [scheduleBody_list]
  exact .bind (listShape _ _ _ (scheduleStepShape stack budget)) scheduleFinishShape

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Scheduler.Points
