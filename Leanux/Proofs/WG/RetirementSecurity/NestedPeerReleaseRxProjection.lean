import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseProjection

/-! Exact RX callback contracts; disposal before a later Stop is retained. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem rx_publish_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (irq : WGPrefix E Unit) (irq' : WGPrefix F Unit) (skb : SkbId) (state : PacketState) (hirq : StateProjectsPrefix ρ id irq irq') :
    StateProjectsPrefix ρ id (publishWith g irq skb state) (publishWith t irq' skb state) := by
  unfold publishWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hirq
    | nested_release_project h ρ

theorem rx_admit_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (allocate : RxPacket → WGPrefix E SkbId) (allocate' : RxPacket → WGPrefix F SkbId) (msg : Key) (src : SkbSource) (ds : Nat) (hallocate : ∀ x, StateProjectsPrefix ρ id (allocate x) (allocate' x)) :
    StateProjectsPrefix ρ id (admitWith g allocate msg src ds) (admitWith t allocate' msg src ds) := by
  unfold admitWith RxOrigin.admitWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hallocate _
    | nested_release_project h ρ

theorem rx_ingressFinish_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (publish : SkbId → WGPrefix E Unit) (publish' : SkbId → WGPrefix F Unit) (a : RxOrigin.Admission) (hpublish : ∀ x, StateProjectsPrefix ρ id (publish x) (publish' x)) :
    StateProjectsPrefix ρ id (ingressFinishWith g publish a) (ingressFinishWith t publish' a) := by
  unfold ingressFinishWith RxOrigin.finishWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hpublish _
    | nested_release_project h ρ

theorem rx_ingress_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (msg : Key) (src : SkbSource) (ds : Nat) :
    StateProjectsPrefix ρ id (ingress g msg src ds) (ingress t msg src ds) := by
  unfold ingress ingressWith ingressFinishWith RxOrigin.finishWith admitWith RxOrigin.admitWith publishWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_project h ρ

theorem rx_rxAfterLookup_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) (ready : Packets.RxReady) (routed : Option PeerId) :
    StateProjectsPrefix ρ id (rxAfterLookupWith g pid ready routed) (rxAfterLookupWith t pid ready routed) := by
  unfold rxAfterLookupWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_project h ρ

theorem rx_rxFinish_projects (ρ : E → Option F) (h : Ops.Projects ρ g t) (pid : PeerId) (ready : Packets.RxReady) :
    StateProjectsPrefix ρ id (rxFinishWith g pid ready) (rxFinishWith t pid ready) := by
  unfold rxFinishWith rxAfterLookupWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_project h ρ

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
