import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixSendWorker

/-! Native frames used by the bounded send/clear drain. A thrown stop has
no successful native continuation on which the projected state can change. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.SendDrainFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes

theorem stop (reason : Stop) : SameView StagedEntry.view (throw reason : WG.M α) := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a value v b performed
  cases performed

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.SendDrainFrames
