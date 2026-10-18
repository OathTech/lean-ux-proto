import Leanux.Proofs.WG.TransmitSecurity.NonceDeferredSafety

/-! Initial receive admission changes queues and reference counts, but cannot
reset the sending nonce frontier of a retained key allocation. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem rx_enqueue (id : SkbId) : SameView view (enqueuePerDeviceAndPeerRx id) :=
  full (Origins.Retaining.enqueuePerDeviceAndPeerRx_material id)
    (Keypairs.WGMore.enqueuePerDeviceAndPeerRx_sameSnapshot id)

theorem rx_publish_inline (id : SkbId) (state : PacketState) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (enqueuePerPeerRx (pure ()) id state : WG.M Unit) := by
  unfold enqueuePerPeerRx
  simp (config := {zeta := false}) only [invariant,monadLift_self]
  repeat' first
    | (rx_retention_head setRxSkb; exact native_frame h (skb _))
    | nonce_poll_native_step h

theorem rx_admit (msg : List UInt8) (src : SkbSource) (ds : Nat) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (consumeData msg src ds) := by
  unfold consumeData keypairGetNull WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head indexLookup; exact index_lookup _ _ h)
    | (rx_retention_head keypairGet; exact key_get _ h)
    | (rx_retention_head newRxSkb; exact native_frame h (skb _))
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact native_frame h (rx_enqueue _))
    | (rx_retention_head enqueuePerPeerRx; exact rx_publish_inline _ _ h)
    | nonce_poll_native_step h

theorem rx_entry (msg : List UInt8) (src : SkbSource) (h : List Allocation) :
    Preserves (fun w => Inv (view w) h) (wgReceive msg src) := by
  unfold wgReceive packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,invariant,unsupported,queueDeviceWork]
  repeat' first
    | (rx_retention_head consumeData; exact rx_admit _ _ _ h)
    | (rx_retention_head prepareSkbHeader; exact native_frame h ((prepareSkbHeader_sameWGWorld _).factor view))
    | (rx_retention_head ipTunnelGetDsfield; exact native_frame h ((ipTunnelGetDsfield_sameWGWorld _ _).factor view))
    | nonce_poll_native_step h

theorem wg_store (h : List Allocation) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : Inv (view w.wg) h) :
    Inv (view v.wg) h := by
  have projected := congrArg (fun s : WGStoreView => View.mk s.keypairCounter
    (fun id => (s.dev.bind fun d => d.keypairs[id]?).map Nonce.cell)) same
  change view v.wg = view w.wg at projected
  simpa only [projected] using hi

theorem loopback (sites : List HiddenSite) (raised : Bool) : SameView view (loopbackSend sites raised) := by
  intro initial
  change Preserves (fun w => view w = initial) _
  unfold loopbackSend raiseLoopbackRx loopbackSoftirq
  simp (config := {zeta := false}) only [invariant,unsupported,skipCut,getAmbient,peekHiddenSite,hidden]
  repeat' first
    | (rx_retention_head getDev; exact device_read.wp (· = initial))
    | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ hi => hi) (fun _ _ hi => hi.2))
    | nonce_frame_step initial

theorem multicast (family addr : Nat) (h : List Allocation) :
    Preserves (fun w : World => Inv (view w.wg) h) (Env.xmitMulticastLoop family addr) := by
  have native : Preserves (fun w : World => Inv (view w.wg) h)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (native_frame h (loopback [] true))
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Inv (view w.wg) h) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  routing_tx_source [Env.xmitMulticastLoop] using [native,ambient]

end Leanux.Proofs.WG.TransmitSecurity.Nonce.Frames
