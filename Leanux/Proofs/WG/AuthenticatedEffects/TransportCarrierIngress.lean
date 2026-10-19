import Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrierDeferred

/-! Native ingress creates only unencrypted packet cells. The observed peer
repayments preserve the same publication carrier at their actual source cuts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity.Driver
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
variable {E : Type} {extra : List E → Prop}
  {origin : E → Option TransportDriver.OriginEvent} {replay : E → Option TransportDriver.Replay}
  {hooks : Hooks E}

private theorem next_cpu : StateSafe extra origin replay (liftWGPrefix cpumaskNextOnline) := by
  apply state_native
  exact pinned_const _private.Leanux.Proofs.WG.AuthenticatedEffects.TransportPublicationIngress.«0».Leanux.Proofs.WG.AuthenticatedEffects.TransportPublication.nextCpu

macro "transport_ingress_native" : tactic => `(tactic| first
  | (transport_carrier_native indexLookup; exact state_native _ (TransportPublication.indexLookup_preserves _ _))
  | (transport_carrier_native keypairGet; exact state_native _ (TransportPublication.keypairGet_preserves _))
  | (transport_carrier_native keypairGetNull; exact state_native _ (TransportPublication.store_preserves keypairGetNull_sameStore))
  | (transport_carrier_native enqueuePerDeviceAndPeerRx; exact state_native _ (TransportPublication.enqueuePerDeviceAndPeerRx_preserves _))
  | (transport_carrier_native freeRxSkb; exact state_native _ (TransportPublication.freeRxSkb_preserves _))
  | (transport_carrier_native RxWorkers.publishSource; exact state_native _ (TransportPublication.publish_noncrypted_preserves _ .dead (by decide)))
  | (transport_carrier_native newRxSkb; apply state_native; intro history; apply TransportPublication.newRxSkb_preserves; intro impossible; cases impossible)
  | (transport_carrier_native prepareSkbHeader; exact state_rx _ ((prepareSkbHeader_sameWGWorld _).factor RxDisposition.nativeRxStore))
  | (transport_carrier_native ipTunnelGetDsfield; exact state_rx _ ((ipTunnelGetDsfield_sameWGWorld _ _).factor RxDisposition.nativeRxStore))
  | (transport_carrier_native cpumaskNextOnline; exact next_cpu)
  | (transport_carrier_native modifyDev; apply state_rx; apply modifyDev_rx <;> intro d <;> rfl)
  | (transport_carrier_native queueDeviceWork; apply state_rx; unfold queueDeviceWork; transport_native_rx)
  | (transport_carrier_head liftWGPrefix; solve | apply state_rx; transport_effect_rx))

theorem ingress_nested (release : ∀ peer, StateSafe extra origin replay (hooks.peerRelease peer))
    (msg : Key) (src : SkbSource) (ds : Nat) :
    StateSafe extra origin replay (RetirementSecurity.NestedPeerRelease.ingress (nestedOps hooks) msg src ds) := by
  unfold RetirementSecurity.NestedPeerRelease.ingress RetirementSecurity.NestedPeerRelease.ingressWith
    RetirementSecurity.NestedPeerRelease.admitWith RxOrigin.admitWith
    RetirementSecurity.NestedPeerRelease.ingressFinishWith RxOrigin.finishWith
    RetirementSecurity.NestedPeerRelease.publishWith
  simp only [nestedOps,monadLift_self]
  repeat' first
    | (transport_carrier_head Hooks.peerRelease; exact release _)
    | transport_ingress_native
    | transport_carrier_state_step

theorem receive_entry_nested (release : ∀ peer, StateSafe extra origin replay (hooks.peerRelease peer))
    (msg : Key) (src : SkbSource) :
    ProductSafe extra origin replay (receiveEntryObserved hooks msg src) := by
  apply product_state
  unfold RetirementSecurity.NestedPeerRelease.receive RetirementSecurity.NestedPeerRelease.receiveWith
    RetirementSecurity.NestedPeerRelease.packetReceiveWith
  simp only [nestedOps]
  repeat' first
    | (transport_carrier_head RetirementSecurity.NestedPeerRelease.ingress; exact ingress_nested release _ _ _)
    | transport_ingress_native
    | transport_carrier_state_step

end Leanux.Proofs.WG.AuthenticatedEffects.TransportCarrier
