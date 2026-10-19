import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseObserved

/-! Concrete projection-specific history frame for nested disposal callbacks. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects HandshakeSecurity

theorem observedOps_frames (record : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (record e) = none) : Ops.Frames ρ (observedOps record decode) where
  step := by intro α action w a h; rfl
  release := fun peer w => focusPrefix_other record decode ρ quiet ((StagedDisposal.releaseObserved peer).run w)

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
