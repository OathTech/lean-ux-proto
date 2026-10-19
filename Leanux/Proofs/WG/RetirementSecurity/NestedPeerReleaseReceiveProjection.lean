import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseReceiveSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxProjection

/-! Exact callback transport for the original packet-receive entry. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem packetReceive_projects (ρ : E → Option F) {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)} (h : Ops.Projects ρ g t)
    (consume : Key → SkbSource → Nat → WGPrefix E Unit)
    (consume' : Key → SkbSource → Nat → WGPrefix F Unit)
    (hc : ∀ msg src ds, StateProjectsPrefix ρ id (consume msg src ds) (consume' msg src ds))
    (msg : Key) (src : SkbSource) :
    StateProjectsPrefix ρ id (packetReceiveWith g consume msg src)
      (packetReceiveWith t consume' msg src) := by
  unfold packetReceiveWith
  repeat' first
    | with_reducible exact hc _ _ _
    | nested_release_project h ρ

theorem receiveWith_projects (ρ : E → Option F) {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)} (h : Ops.Projects ρ g t)
    (consume : Key → SkbSource → Nat → WGPrefix E Unit)
    (consume' : Key → SkbSource → Nat → WGPrefix F Unit)
    (hc : ∀ msg src ds, StateProjectsPrefix ρ id (consume msg src ds) (consume' msg src ds))
    (msg : Key) (src : SkbSource) :
    StateProjectsPrefix ρ id (receiveWith g consume msg src)
      (receiveWith t consume' msg src) := by
  unfold receiveWith
  repeat' first
    | with_reducible exact packetReceive_projects ρ h consume consume' hc _ _
    | nested_release_project h ρ

theorem receive_projects (ρ : E → Option F) {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)} (h : Ops.Projects ρ g t)
    (msg : Key) (src : SkbSource) :
    StateProjectsPrefix ρ id (receive g msg src) (receive t msg src) := by
  exact receiveWith_projects ρ h _ _ (rx_ingress_projects ρ h) msg src

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
