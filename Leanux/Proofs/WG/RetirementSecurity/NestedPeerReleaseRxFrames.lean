import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseFrames

/-! Exact RX callback contracts; disposal before a later Stop is retained. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem rx_publish_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (irq : WGPrefix E Unit) (skb : SkbId) (state : PacketState) (hirq : StateHistoryFrame ρ irq) :
    StateHistoryFrame ρ (publishWith g irq skb state) := by
  unfold publishWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hirq
    | nested_release_frame h ρ

theorem rx_admit_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (allocate : RxPacket → WGPrefix E SkbId) (msg : Key) (src : SkbSource) (ds : Nat) (hallocate : ∀ x, StateHistoryFrame ρ (allocate x)) :
    StateHistoryFrame ρ (admitWith g allocate msg src ds) := by
  unfold admitWith RxOrigin.admitWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hallocate _
    | nested_release_frame h ρ

theorem rx_ingressFinish_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (publish : SkbId → WGPrefix E Unit) (a : RxOrigin.Admission) (hpublish : ∀ x, StateHistoryFrame ρ (publish x)) :
    StateHistoryFrame ρ (ingressFinishWith g publish a) := by
  unfold ingressFinishWith RxOrigin.finishWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hpublish _
    | nested_release_frame h ρ

theorem rx_ingress_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (msg : Key) (src : SkbSource) (ds : Nat) :
    StateHistoryFrame ρ (ingress g msg src ds) := by
  unfold ingress ingressWith ingressFinishWith RxOrigin.finishWith admitWith RxOrigin.admitWith publishWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_frame h ρ

theorem rx_rxAfterLookup_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) (ready : Packets.RxReady) (routed : Option PeerId) :
    StateHistoryFrame ρ (rxAfterLookupWith g pid ready routed) := by
  unfold rxAfterLookupWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_frame h ρ

theorem rx_rxFinish_frame (ρ : E → Option F) (h : Ops.Frames ρ g) (pid : PeerId) (ready : Packets.RxReady) :
    StateHistoryFrame ρ (rxFinishWith g pid ready) := by
  unfold rxFinishWith rxAfterLookupWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_frame h ρ

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
