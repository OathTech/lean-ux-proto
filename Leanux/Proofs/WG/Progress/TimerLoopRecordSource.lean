import Leanux.Proofs.WG.Progress.TimerUnitRecordSource
import Leanux.Proofs.WG.Progress.DeliverySuffixSource
/-! Normal suffix effects of the entire original timer loop, including
selected timer/send/clear sections, crypt scheduling and the final checks. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing
open Leanux.Proofs.WG.TimerDiscipline

theorem timerOuterTurn_retains
    (records : List HiddenRecord) (bound : UInt64) (turn : Nat) (state : Bool × Option UInt64) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (timerOuterTurn bound turn state) := by
  have dev : Preserves (fun w : World=>Tail records w.ambient.hidden) (getDev : Leanux.M Device) :=
    native_product records _ (native_getDev records)
  have clear : Preserves (fun w : World=>Tail records w.ambient.hidden) Env.runOneClearWorker :=
    hoare_consequence (clearWorker_strict records) (fun _ h=>h) (fun _ _ h=>strict_tail h)
  have send : Preserves (fun w : World=>Tail records w.ambient.hidden) Env.runOneSendWorker :=
    hoare_consequence (sendWorker_strict records) (fun _ h=>h) (fun _ _ h=>strict_tail h)
  have stop {α : Type} (e : Stop) :
      Preserves (fun w : World=>Tail records w.ambient.hidden) (throw e : Leanux.M α) := hoare_throw e
  unfold timerOuterTurn
  repeat' first
    | env_operation_fact peekNextSite_retains
    | env_operation_fact dev
    | env_operation_fact clear
    | env_operation_fact send
    | env_operation_fact requireStepComplete_retains
    | env_operation_fact timerDispatchUnit_retains
    | env_operation_fact runCryptWorkers_retains
    | env_operation_fact stop
    | with_reducible exact preserves_pure _
    | with_reducible apply preserves_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem timerOuterFinish_retains (records : List HiddenRecord) (state : Bool × Option UInt64) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (timerOuterFinish state) := by
  have dev : Preserves (fun w : World=>Tail records w.ambient.hidden) (getDev : Leanux.M Device) :=
    native_product records _ (native_getDev records)
  have fail {α : Type} (message : String) :
      Preserves (fun w : World=>Tail records w.ambient.hidden) (unsupported message : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
  unfold timerOuterFinish
  repeat' first
    | env_operation_fact requireStepComplete_retains
    | env_operation_fact dev
    | env_operation_fact deliverSent_retains
    | env_operation_fact fail
    | with_reducible exact preserves_pure _
    | with_reducible apply preserves_bind
    | split
    | (with_reducible intro x; try dsimp only)

theorem runTimers_retains
    (records : List HiddenRecord) (bound : UInt64) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.runTimers bound) := by
  rw [←runTimers_loop_source]
  unfold runTimersLoopSource
  apply preserves_bind (native_product records _
    (native_modify records (fun g=>{g with queuedThisCall:=[]})))
  intro _
  apply preserves_bind (stack_getWG_retains records)
  intro g
  split
  · exact preserves_pure _
  · apply preserves_bind (recordBudget_retains records)
    intro budget
    apply preserves_bind
    · simp only [Std.Legacy.Range.forIn_eq_forIn_range']
      apply list_view_spec (fun w : World=>w.ambient.hidden) (Tail records)
      intro i state
      exact timerOuterTurn_retains records bound i state
    intro state
    exact timerOuterFinish_retains records state

end Leanux.Proofs.WG.Progress.RecordSuffix
