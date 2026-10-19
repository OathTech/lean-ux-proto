import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseReceiveSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxFrames

/-! Exact callback transport for the original packet-receive entry. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem packetReceive_frame (ρ : E → Option F) {g : Ops (WGPrefix E)}
    (h : Ops.Frames ρ g) (consume : Key → SkbSource → Nat → WGPrefix E Unit)
    (hc : ∀ msg src ds, StateHistoryFrame ρ (consume msg src ds))
    (msg : Key) (src : SkbSource) :
    StateHistoryFrame ρ (packetReceiveWith g consume msg src) := by
  unfold packetReceiveWith
  repeat' first
    | with_reducible exact hc _ _ _
    | nested_release_frame h ρ

theorem receiveWith_frame (ρ : E → Option F) {g : Ops (WGPrefix E)}
    (h : Ops.Frames ρ g) (consume : Key → SkbSource → Nat → WGPrefix E Unit)
    (hc : ∀ msg src ds, StateHistoryFrame ρ (consume msg src ds))
    (msg : Key) (src : SkbSource) :
    StateHistoryFrame ρ (receiveWith g consume msg src) := by
  unfold receiveWith
  repeat' first
    | with_reducible exact packetReceive_frame ρ h consume hc _ _
    | nested_release_frame h ρ

theorem receive_frame (ρ : E → Option F) {g : Ops (WGPrefix E)}
    (h : Ops.Frames ρ g) (msg : Key) (src : SkbSource) :
    StateHistoryFrame ρ (receive g msg src) :=
  receiveWith_frame ρ h _ (rx_ingress_frame ρ h) msg src

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
