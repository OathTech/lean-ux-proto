import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionConfiguration
import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialLifecycleFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

/-- One-call lifecycle retention from `Noise.PendingTickets.wgDown_retained`
and `wgCreate_retained` at C2 pin
`7ff94e48c2a3323ef29e6fb62f82a4a64d43f218`. No event-history premise occurs. -/
structure H1LifecycleFrames : Prop where
  down : ProjectedAction view Retained wgDown
  create : ProjectedAction view Retained wgCreate

theorem socket_frame {action : WG.M α} (same : SameSocket action) : SameView view action := by
  apply same.of_factor (fun s : WGOwnedView => view {dev:=s.dev,keypairCounter:=s.keypairCounter}) view
  intro w
  unfold view nextSlot keypairResidents
  simp only [socketView,wgOwnedView,wgStoreView,Option.bind_map]
  rfl

theorem Carrier.socket {action : WG.M α} (same : SameSocket action) (confirmed : List Nat) :
    Preserves (Carrier confirmed) action :=
  Carrier.from_frame (Responder.DriverCuts.carrier_socket same) (socket_frame same) confirmed

theorem Carrier.down (frames : H1LifecycleFrames) (confirmed : List Nat) :
    Preserves (Carrier confirmed) wgDown :=
  Carrier.bounds confirmed ResidentMaterial.bounds_down (PendingPromotion.preserves frames.down confirmed)

theorem Carrier.create (frames : H1LifecycleFrames) (confirmed : List Nat) :
    Preserves (Carrier confirmed) wgCreate :=
  Carrier.bounds confirmed ResidentMaterial.bounds_create (PendingPromotion.preserves frames.create confirmed)

theorem Carrier.limiter (confirmed : List Nat) : Preserves (Carrier confirmed) ratelimiterUninit := by
  apply Carrier.from_frame Responder.DriverCuts.carrier_limiter _ confirmed
  apply ratelimiterUninit_sameRatelimiter.of_factor (fun s : WGStoreView =>
    view {dev:=s.dev,keypairCounter:=s.keypairCounter}) view
  intro w
  rfl

theorem Carrier.drop_device (confirmed : List Nat) :
    Preserves (Carrier confirmed) (modify (fun w : WGWorld => {w with dev:=none}) : WG.M Unit) := by
  apply hoare_modify
  intro w hi
  refine ⟨(ResidentMaterial.bounds_absent _ rfl).1,(ResidentMaterial.bounds_absent _ rfl).2,
    hi.2.2.retained ?_⟩
  exact ⟨rfl,by intro pid stamp impossible; cases impossible⟩

theorem Carrier.destruct (frames : H1ConfigurationFrames) (confirmed : List Nat) :
    Preserves (Carrier confirmed) wgDestruct := by
  unfold wgDestruct
  simp (config := {zeta := false}) only [unsupported,invariant]
  repeat' first
    | (rx_retention_head socketReinit; exact Carrier.socket (socketReinit_sameSocket _ _) confirmed)
    | (rx_retention_head peerRemoveAll; exact Carrier.remove_all frames confirmed)
    | (rx_retention_head mayHaveSlept; exact Carrier.store confirmed mayHaveSlept_sameWGStore)
    | (rx_retention_head ratelimiterUninit; exact Carrier.limiter confirmed)
    | (rx_retention_head modify; exact Carrier.drop_device confirmed)
    | (rx_retention_head retireDeviceUnits; exact Carrier.store confirmed retireDeviceUnits_sameWGStore)
    | pending_carrier_ingress_step (), confirmed

theorem Carrier.pre_exit (frames : H1ConfigurationFrames) (confirmed : List Nat) :
    Preserves (Carrier confirmed) netnsPreExit := by
  unfold netnsPreExit
  simp (config := {zeta := false}) only [branch]
  repeat' first
    | (rx_retention_head get
       exact hoare_consequence (hoare_get (Carrier confirmed)) (fun _ hi => hi) (fun _ _ hi => hi.2))
    | (rx_retention_head socketReinit; exact Carrier.socket (socketReinit_sameSocket _ _) confirmed)
    | (rx_retention_head clearPeerEndpointSrc
       exact Carrier.from_frame (Responder.DriverCuts.carrier_clear_endpoint _) (frames.endpoint _) confirmed)
    | (rx_retention_head ForIn.forIn
       apply list_view_spec id (Carrier confirmed)
       intro x b
       change Preserves (Carrier confirmed) _)
    | pending_carrier_ingress_step (), confirmed

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
