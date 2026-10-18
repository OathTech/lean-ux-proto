import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverDeviceConfig
import Leanux.Proofs.WG.HandshakeSecurity.ResponderIngress
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.Lifetimes.TxCallSource

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem carrier_rx_enqueue (id : SkbId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (enqueuePerDeviceAndPeerRx id) :=
  carrier_frame confirmed
    ((pinned_const _private.Leanux.Proofs.WG.Origins.CurrentRx.«0».Leanux.Proofs.WG.CurrentRx.enqueuePerDeviceAndPeerRx_view) id)
    (enqueueRx_native id confirmed)

theorem carrier_rx_dead (id : SkbId) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (enqueuePerPeerRx (Pure.pure () : WG.M Unit) id .dead) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (carrier_rx_publish id .dead confirmed) (fun pid =>
    preserves_bind (preserves_pure ()) (fun _ => carrier_peer_put (some pid) confirmed))

theorem carrier_rx_admit (msg : List UInt8) (src : SkbSource) (ds : Nat) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keypairGet; exact carrier_borrow _ confirmed)
    | (rx_retention_head keypairGetNull; exact carrier_store keypairGetNull_sameStore confirmed)
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact carrier_rx_enqueue _ confirmed)
    | (rx_retention_head enqueuePerPeerRx; exact carrier_rx_dead _ confirmed)
    | (rx_retention_head newRxSkb; unfold newRxSkb; exact carrier_skb _ confirmed)
    | responder_carrier_handshake_step confirmed

theorem carrier_rx_entry (msg : List UInt8) (src : SkbSource) (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) (wgReceive msg src) := by
  unfold wgReceive packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,invariant,unsupported,queueDeviceWork]
  repeat' first
    | (rx_retention_head consumeData; exact carrier_rx_admit _ _ _ confirmed)
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (Carrier confirmed))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (Carrier confirmed))
    | responder_carrier_handshake_step confirmed

theorem product_wg_stable (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : ProductInv h w) : ProductInv h v := by
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  refine ⟨⟨?_,hi.1.2.1.frame ?_,CurrentSlots.fields_transport hi.1.2.2 ?_⟩,hi.2⟩
  · intro s hs
    apply hi.1.1 s
    simpa only [ConfiguredIdentity.view,device] using hs
  · unfold current
    rw [device]
  · unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]

theorem carrier_multicast (family addr : Nat) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) (Env.xmitMulticastLoop family addr) := by
  have native : Framing.Preserves (fun w : World => Carrier confirmed w.wg)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (carrier_store (loopbackSend_kernel [] true) confirmed)
  have ambient {α : Type} (a : AmbientM α) :
      Framing.Preserves (fun w : World => Carrier confirmed w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  routing_tx_source [Env.xmitMulticastLoop] using [native,ambient]

end Leanux.Proofs.WG.HandshakeSecurity.Responder.DriverCuts
