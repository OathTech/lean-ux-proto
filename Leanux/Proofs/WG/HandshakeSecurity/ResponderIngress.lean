import Leanux.Proofs.WG.HandshakeSecurity.ResponderDeviceFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues Origins Origins.Retaining

theorem borrowKey_native (kid : Option KeypairId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (keypairGet kid) :=
  native_join ((keypairGet_current kid).wp (fun f =>
    ∀ pid core, f pid = some core → core.initiator = false → core.allocation ∈ confirmed))
    (CurrentSlots.keypairGet_preserves kid)

theorem enqueueRx_native (id : SkbId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (enqueuePerDeviceAndPeerRx id) :=
  native_fields (pool_of_material (enqueuePerDeviceAndPeerRx_material id))
    (CurrentSlots.enqueuePerDeviceAndPeerRx_fields id) confirmed

theorem enqueueDead_native (id : SkbId) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (enqueuePerPeerRx (pure () : WG.M Unit) id .dead) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (publish_native id .dead confirmed) (fun pid =>
    preserves_bind (preserves_pure ()) (fun _ => peerPut_native (some pid) confirmed))

theorem consumeIngress_native (msg : List UInt8) (src : SkbSource) (ds : Nat) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch, invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact indexLookup_native _ _ confirmed)
    | (rx_retention_head keypairGet; exact borrowKey_native _ confirmed)
    | (rx_retention_head keypairGetNull; exact native_store keypairGetNull_sameStore confirmed)
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact enqueueRx_native _ confirmed)
    | (rx_retention_head enqueuePerPeerRx; exact enqueueDead_native _ confirmed)
    | (rx_retention_head keypairPut; exact keypairPut_native _ _ confirmed)
    | (rx_retention_head newRxSkb; unfold newRxSkb; exact native_skb _ confirmed)
    | (rx_retention_head freeRxSkb; unfold freeRxSkb; exact native_skb _ confirmed)
    | responder_config_step confirmed

theorem nextCpu_native (confirmed : List Nat) :
    Preserves (History.Native confirmed) cpumaskNextOnline := by
  unfold cpumaskNextOnline
  simp (config := {zeta := false}) only [branch]
  repeat' responder_config_step confirmed

theorem packetReceive_native (msg : List UInt8) (src : SkbSource) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (WG.packetReceive msg src) := by
  unfold WG.packetReceive
  simp (config := {zeta := false}) only [branch, queueDeviceWork, unsupported, invariant]
  repeat' first
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (History.Native confirmed))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (History.Native confirmed))
    | (rx_retention_head consumeData; exact consumeIngress_native _ _ _ confirmed)
    | (rx_retention_head cpumaskNextOnline; exact nextCpu_native confirmed)
    | responder_config_step confirmed

theorem wgReceive_native (msg : List UInt8) (src : SkbSource) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (WG.wgReceive msg src) := by
  unfold WG.wgReceive
  simp (config := {zeta := false}) only [branch, unsupported]
  repeat' first
    | (rx_retention_head WG.packetReceive; exact packetReceive_native _ _ confirmed)
    | responder_config_step confirmed

theorem Joint.ingress (msg : List UInt8) (src : SkbSource) :
    Joint.Preserves (RxHistory.mixed (liftWGObserver (wgReceivePrefix msg src))) :=
  Joint.from_global _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.receive) msg src)
    (Global.native_mixed _ _ (wgReceivePrefix_erases msg src) (wgReceive_native msg src))

theorem Joint.transmit (family addr : Nat) (packets : List WG.Packet) (mtu : Nat) :
    Joint.Preserves (RxHistory.mixed (liftWGObserver (wgXmitPrefix family addr packets mtu))) :=
  Joint.from_global _
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTraffic.«0».Leanux.Proofs.WG.PublicationTraffic.transmit) family addr packets mtu)
    (Global.native_mixed _ _ (wgXmitPrefix_erases family addr packets mtu)
      (wgXmit_native family addr packets mtu))

end Leanux.Proofs.WG.HandshakeSecurity.Responder
