import Leanux.Proofs.WG.HandshakeSecurity.PeerReferenceDeferred
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.Lifetimes.TxCallSource

/-! Native datagram admission retains peer-allocation timestamp;
queue failures and their deleting releases use the actual source paths. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem rx_enqueue (id : SkbId) :
    Framing.Preserves Inv (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRx
  apply preserves_bind (skb _)
  intro _
  apply preserves_bind (skb _)
  intro pkt
  apply hoare_bind _ _ (read_saved pkt.peer)
  intro p
  apply hoare_bind _ _ (hoare_liftAmbient
    (AmbientM.branch .enqueuePeerQueueFull (p.rxQueue.count ≥ MAX_QUEUED_PACKETS)) _)
  intro full
  cases full with
  | true =>
    exact hoare_consequence (preserves_pure _)
      (fun _ hi => hi.1) (fun _ _ hi => hi)
  | false =>
    apply hoare_bind _ _ (write_saved pkt.peer p
      (fun current => {current with rxQueue := p.rxQueue.enqueue id}) (fun _ => rfl))
    intro _
    change Framing.Preserves Inv _
    simp (config := {zeta := false}) only [cpumaskNextOnlineFrom,queueDeviceWork,branch]
    repeat' peer_reference_poll_step

theorem rx_dead (id : SkbId) :
    Framing.Preserves Inv (enqueuePerPeerRx (Pure.pure () : WG.M Unit) id .dead) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (rx_publish id .dead) (fun pid =>
    preserves_bind (preserves_pure ()) (fun _ => peer_put (some pid)))

theorem rx_admit (msg : List UInt8) (src : SkbSource) (ds : Nat) :
    Framing.Preserves Inv (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keypairGetNull; exact store keypairGetNull_sameStore)
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact rx_enqueue _)
    | (rx_retention_head enqueuePerPeerRx; exact rx_dead _)
    | (rx_retention_head newRxSkb; unfold newRxSkb; exact skb _)
    | peer_reference_poll_step

theorem rx_entry (msg : List UInt8) (src : SkbSource) :
    Framing.Preserves Inv (wgReceive msg src) := by
  unfold wgReceive packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,invariant,unsupported,queueDeviceWork]
  repeat' first
    | (rx_retention_head consumeData; exact rx_admit _ _ _)
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp Inv)
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp Inv)
    | peer_reference_poll_step

theorem product_wg_stable (h : List Exchange.Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : ProductInv h w) : ProductInv h v := by
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  refine ⟨hi.1,of_residents ?_⟩
  intro d pid peer found stored
  exact resident hi.2 (device.symm.trans found) stored

theorem multicast_native (family addr : Nat) :
    Framing.Preserves (fun w : World => Inv w.wg) (Env.xmitMulticastLoop family addr) := by
  have native : Framing.Preserves (fun w : World => Inv w.wg)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (store (loopbackSend_kernel [] true))
  have ambient {α : Type} (a : AmbientM α) :
      Framing.Preserves (fun w : World => Inv w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  routing_tx_source [Env.xmitMulticastLoop] using [native,ambient]

end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
