import Leanux.Proofs.WG.Progress.TimerLoopRecordSource
import Leanux.Proofs.WG.Progress.BatchDrainSource
/-! Normal suffix retention through the exact original recorded batch loop.
The following completion guard is outside this claim. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem afterBatchRecordedLoop_retains (records : List HiddenRecord) :
    Preserves (fun w : World=>Tail records w.ambient.hidden) afterBatchRecordedLoop := by
  have dev : Preserves (fun w : World=>Tail records w.ambient.hidden) (getDev : Leanux.M Device) :=
    native_product records _ (native_getDev records)
  have send : Preserves (fun w : World=>Tail records w.ambient.hidden) Env.runOneSendWorker :=
    hoare_consequence (sendWorker_strict records) (fun _ h=>h) (fun _ _ h=>strict_tail h)
  unfold afterBatchRecordedLoop
  apply preserves_bind (recordBudget_retains records)
  intro budget
  simp only [Std.Legacy.Range.forIn_eq_forIn_range']
  apply preserves_bind
  · apply list_view_spec (fun w : World=>w.ambient.hidden) (Tail records)
    intro index state
    change Preserves (fun w : World=>Tail records w.ambient.hidden) _
    repeat' first
      | env_operation_fact schedule_retains
      | env_operation_fact peekNextSite_retains
      | env_operation_fact dev
      | env_operation_fact send
      | with_reducible exact preserves_pure _
      | with_reducible apply preserves_bind
      | split
      | (with_reducible intro x; try dsimp only)
  intro _
  exact preserves_pure _

end Leanux.Proofs.WG.Progress.RecordSuffix
