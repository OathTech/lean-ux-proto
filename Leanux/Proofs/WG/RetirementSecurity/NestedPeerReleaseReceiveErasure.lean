import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseReceiveSource
import Leanux.Proofs.WG.RetirementSecurity.NestedPeerReleaseRxErasure

/-! Exact callback transport for the original packet-receive entry. -/
namespace Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
open Leanux Leanux.WG Leanux.Proofs.Logged AuthenticatedEffects
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

theorem packetReceive_erases {g : Ops (WGPrefix E)} (h : Ops.Erases g)
    (consume : Key → SkbSource → Nat → WGPrefix E Unit)
    (consume' : Key → SkbSource → Nat → WG.M Unit)
    (hc : ∀ msg src ds, ErasesStatePrefix (consume msg src ds) (consume' msg src ds))
    (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (packetReceiveWith g consume msg src)
      (packetReceiveWith native consume' msg src) := by
  unfold packetReceiveWith
  repeat' first
    | with_reducible exact hc _ _ _
    | nested_release_erase h

theorem receiveWith_erases {g : Ops (WGPrefix E)} (h : Ops.Erases g)
    (consume : Key → SkbSource → Nat → WGPrefix E Unit)
    (consume' : Key → SkbSource → Nat → WG.M Unit)
    (hc : ∀ msg src ds, ErasesStatePrefix (consume msg src ds) (consume' msg src ds))
    (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (receiveWith g consume msg src)
      (receiveWith native consume' msg src) := by
  unfold receiveWith
  repeat' first
    | with_reducible exact packetReceive_erases h consume consume' hc _ _
    | nested_release_erase h

theorem receive_erases {g : Ops (WGPrefix E)} (h : Ops.Erases g)
    (msg : Key) (src : SkbSource) :
    ErasesStatePrefix (receive g msg src) (wgReceive msg src) := by
  rw [←receive_native]
  exact receiveWith_erases h _ _ (rx_ingress_erases h) msg src

end Leanux.Proofs.WG.RetirementSecurity.NestedPeerRelease
