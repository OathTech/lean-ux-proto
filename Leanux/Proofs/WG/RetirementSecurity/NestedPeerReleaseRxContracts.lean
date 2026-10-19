import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxErasure
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxFrames
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxProjection
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseObservedFrames

/-! Native and old-journal contracts for all ingress refusal/publication
repayments and the routed-source repayment, including stopped executions. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects HandshakeSecurity

theorem ingress_lifted (msg : Key) (src : SkbSource) (ds : Nat) :
    ingress (lifted : Ops (WGPrefix E)) msg src ds = liftWGPrefix (consumeData msg src ds) := by
  rw [←ingress_native]
  exact TimerEffects.eq_native_lift (rx_ingress_erases lifted_erases msg src ds)
    (rx_ingress_frame some (lifted_frames some) msg src ds)

theorem rxFinish_lifted (pid : PeerId) (ready : Packets.RxReady) :
    rxFinishWith (lifted : Ops (WGPrefix E)) pid ready = liftWGPrefix (Packets.rxFinish pid ready) := by
  rw [←rxFinish_native]
  exact TimerEffects.eq_native_lift (rx_rxFinish_erases lifted_erases pid ready)
    (rx_rxFinish_frame some (lifted_frames some) pid ready)

/-- Ingress observes the actual refusal, DEAD publication and ENOSPC repayments.
No successful enclosing consumeData return is required by this projection. -/
theorem ingress_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (msg : Key) (src : SkbSource) (ds : Nat) :
    StateProjectsPrefix ρ id (ingress (observedOps release decode) msg src ds)
      (liftWGPrefix (consumeData msg src ds)) := by
  rw [←ingress_lifted]
  exact rx_ingress_projects ρ (observedOps_projects release decode ρ quiet) msg src ds

/-- The routed lookup reference is repaid before the original peer-mismatch
branch. A disposal at this cut survives any later Stop. -/
theorem rxFinish_old (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (ρ : E → Option F)
    (quiet : ∀ e, ρ (release e) = none) (pid : PeerId) (ready : Packets.RxReady) :
    StateProjectsPrefix ρ id (rxFinishWith (observedOps release decode) pid ready)
      (liftWGPrefix (Packets.rxFinish pid ready)) := by
  rw [←rxFinish_lifted]
  exact rx_rxFinish_projects ρ (observedOps_projects release decode ρ quiet) pid ready

theorem ingressObserved_erases (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (msg : Key) (src : SkbSource) (ds : Nat) :
    ErasesStatePrefix (ingress (observedOps release decode) msg src ds) (consumeData msg src ds) := by
  simpa only [ingress_native] using rx_ingress_erases (observedOps_erases release decode) msg src ds

theorem rxFinishObserved_erases (release : StagedDisposal.Event → E)
    (decode : E → Option StagedDisposal.Event) (pid : PeerId) (ready : Packets.RxReady) :
    ErasesStatePrefix (rxFinishWith (observedOps release decode) pid ready) (Packets.rxFinish pid ready) := by
  simpa only [rxFinish_native] using rx_rxFinish_erases (observedOps_erases release decode) pid ready

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
