import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseReceiveErasure
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseReceiveProjection
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseReceiveFrames
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseObservedFrames

/-! Exact native and old-history contracts for the complete UDP ingress.
All rejection, publication and routed reference cuts retain stopped prefixes. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects HandshakeSecurity

theorem receive_lifted (msg : Key) (src : SkbSource) :
    receive (lifted : Ops (WGPrefix E)) msg src = liftWGPrefix (wgReceive msg src) :=
  TimerEffects.eq_native_lift (receive_erases lifted_erases msg src)
    (receive_frame some (lifted_frames some) msg src)

/-- The complete native UDP entry emits each actual nested ingress disposal
before its continuation; hiding only those events recovers the old history,
including any Stop from header validation or a later release suffix. -/
theorem receive_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (msg : Key) (src : SkbSource) :
    StateProjectsPrefix ρ id (receive (observedOps release decode) msg src)
      (liftWGPrefix (wgReceive msg src)) := by
  rw [←receive_lifted]
  exact receive_projects ρ (observedOps_projects release decode ρ quiet) msg src

theorem receiveObserved_erases (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (receive (observedOps release decode) msg src) (wgReceive msg src) :=
  receive_erases (observedOps_erases release decode) msg src

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
