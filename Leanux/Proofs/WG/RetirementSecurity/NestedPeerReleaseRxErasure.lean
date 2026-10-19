import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseErasure

/-! Exact RX callback contracts; disposal before a later Stop is retained. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
variable {g : Ops (WGPrefix E)} {t : Ops (WGPrefix F)}

theorem rx_publish_erases (h : Ops.Erases g) (irq : WGPrefix E Unit) (irq' : WG.M Unit) (skb : SkbId) (state : PacketState) (hirq : ErasesStatePrefix irq irq') :
    ErasesStatePrefix (publishWith g irq skb state) (publishWith native irq' skb state) := by
  unfold publishWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hirq
    | nested_release_erase h

theorem rx_admit_erases (h : Ops.Erases g) (allocate : RxPacket → WGPrefix E SkbId) (allocate' : RxPacket → WG.M SkbId) (msg : Key) (src : SkbSource) (ds : Nat) (hallocate : ∀ x, ErasesStatePrefix (allocate x) (allocate' x)) :
    ErasesStatePrefix (admitWith g allocate msg src ds) (admitWith native allocate' msg src ds) := by
  unfold admitWith RxOrigin.admitWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hallocate _
    | nested_release_erase h

theorem rx_ingressFinish_erases (h : Ops.Erases g) (publish : SkbId → WGPrefix E Unit) (publish' : SkbId → WG.M Unit) (a : RxOrigin.Admission) (hpublish : ∀ x, ErasesStatePrefix (publish x) (publish' x)) :
    ErasesStatePrefix (ingressFinishWith g publish a) (ingressFinishWith native publish' a) := by
  unfold ingressFinishWith RxOrigin.finishWith
  try simp only [monadLift_self]
  repeat' first
    | with_reducible exact hpublish _
    | nested_release_erase h

theorem rx_ingress_erases (h : Ops.Erases g) (msg : Key) (src : SkbSource) (ds : Nat) :
    ErasesStatePrefix (ingress g msg src ds) (ingress native msg src ds) := by
  unfold ingress ingressWith ingressFinishWith RxOrigin.finishWith admitWith RxOrigin.admitWith publishWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_erase h

theorem rx_rxAfterLookup_erases (h : Ops.Erases g) (pid : PeerId) (ready : Packets.RxReady) (routed : Option PeerId) :
    ErasesStatePrefix (rxAfterLookupWith g pid ready routed) (rxAfterLookupWith native pid ready routed) := by
  unfold rxAfterLookupWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_erase h

theorem rx_rxFinish_erases (h : Ops.Erases g) (pid : PeerId) (ready : Packets.RxReady) :
    ErasesStatePrefix (rxFinishWith g pid ready) (rxFinishWith native pid ready) := by
  unfold rxFinishWith rxAfterLookupWith
  try simp only [monadLift_self]
  repeat' first
    | nested_release_erase h

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
