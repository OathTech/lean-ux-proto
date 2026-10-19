import Leanux.Proofs.WG.Progress.SchedulerRecordSource
import Leanux.Proofs.WG.Progress.TimerCallbackSuffixSource
import Leanux.Proofs.WG.TimerDiscipline.OuterFirstTurnSource
/-! Hidden-record frames for original timer-loop observations and refusal guards.
These establish normal suffix retention, not timer matching or guard success. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem peekNextSite_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) Env.peekNextSite := by
  unfold Env.peekNextSite
  apply preserves_bind (getAmbient_retains records)
  intro a
  split <;> exact preserves_pure _

theorem timerWorker_retains (records : List HiddenRecord) (timer : PeerTimer) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.timerWorker timer) := by
  unfold Env.timerWorker
  split
  · exact preserves_pure _
  · apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run

theorem sectionAppearsLater_retains (records : List HiddenRecord) (worker : Worker) (unit : Nat) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.sectionAppearsLater worker unit) := by
  apply (hoare_iff_run _ _ _).mpr
  intro before value after pre run
  cases run
  exact pre

theorem requireStepComplete_retains (records : List HiddenRecord) (step : UInt64) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.requireStepComplete step) := by
  unfold Env.requireStepComplete
  apply preserves_bind (native_product records _ (native_getDev records))
  intro d
  split
  · exact hoare_throw _
  · exact preserves_pure _

theorem requireNothingDue_retains (records : List HiddenRecord) (bound : UInt64) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) (Env.requireNothingDue bound) := by
  have unsupportedKeeps {α : Type} (message : String) :
      Preserves (fun w : World=>Tail records w.ambient.hidden) (unsupported message : Leanux.M α) := by
    apply (hoare_iff_run _ _ _).mpr
    intro before value after pre run
    cases run
  have stop {α : Type} (e : Stop) :
      Preserves (fun w : World=>Tail records w.ambient.hidden) (throw e : Leanux.M α) := hoare_throw e
  unfold Env.requireNothingDue
  repeat' first
    | env_operation_fact stack_getWG_retains
    | env_operation_fact timerWorker_retains
    | env_operation_fact sectionAppearsLater_retains
    | with_reducible exact unsupportedKeeps _
    | env_operation_fact stop
    | with_reducible exact preserves_pure _
    | with_reducible apply preserves_bind
    | split
    | (with_reducible intro x; try dsimp only)
end Leanux.Proofs.WG.Progress.RecordSuffix
