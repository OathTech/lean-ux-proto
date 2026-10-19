import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleEnvironmentSource

/-! Native environment metadata updates preserve the exact packet projection;
they do not create a new ledger or deletion companion. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
open Leanux Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem env_edit_frame (update : EnvWorld→EnvWorld) :
    SameView (fun w : World=>StagedEntry.view w.wg) (modifyEnv update) := by
  apply (ProjectedAction.iff_run _ _ _).mpr
  intro w value v run
  cases run
  rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Environment
