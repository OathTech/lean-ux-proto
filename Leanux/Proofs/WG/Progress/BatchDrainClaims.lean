import Leanux.Proofs.WG.Progress.BatchDrainSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Progress
open Leanux Leanux.WG Leanux.Env

/-- Every normal recorded `afterBatch` return has passed the actual final
drain checks. No pending-work, suspension or fairness conclusion is asserted. -/
theorem afterBatch_recorded_drained :
    Campaign2.Product.Ensures afterBatch
      (fun s => s.ambient.hidden.isSome = true) (fun _ s => BatchDrained s) := by
  intro entry result final recorded run
  rw [afterBatch_recorded_source entry recorded] at run
  have suffix := afterBatchDrainSuffix_drained
  change Noise.Product.Ensures afterBatchDrainSuffix (fun _ => True)
    (fun _ w => BatchDrained (Campaign2.Product.snapshot w)) at suffix
  have any {α : Type} (a : Leanux.M α) : Noise.Product.Ensures a (fun _ => True) (fun _ _ => True) := by
    intro _ _ _ _ _
    trivial
  exact (Noise.Product.ensures_bind _ _ (any _) fun _ =>
    Noise.Product.ensures_bind _ _ (any afterBatchRecordedLoop) (fun _ => suffix))
    entry result final trivial run

end Leanux.Proofs.WG.Progress
