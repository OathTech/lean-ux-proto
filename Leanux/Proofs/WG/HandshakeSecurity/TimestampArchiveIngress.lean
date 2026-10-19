import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveDeferred
import Leanux.Proofs.WG.Lifetimes.TrafficPreservation
import Leanux.Proofs.WG.Lifetimes.TxCallSource

/-! Native datagram admission retains peer-allocation timestamp history;
queue failures and their deleting releases use the actual source paths. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues Origins

theorem rx_enqueue (id : SkbId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (enqueuePerDeviceAndPeerRx id) := by
  unfold enqueuePerDeviceAndPeerRx
  apply preserves_bind (skb _ history)
  intro _
  apply preserves_bind (skb _ history)
  intro pkt
  apply hoare_bind _ _ (read_saved pkt.peer history)
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
      (fun current => {current with rxQueue := p.rxQueue.enqueue id}) (fun _ => ⟨rfl,rfl⟩) history)
    intro _
    change Framing.Preserves (StateInv history) _
    simp (config := {zeta := false}) only [cpumaskNextOnlineFrom,queueDeviceWork,branch]
    repeat' archive_poll_step history

theorem rx_dead (id : SkbId) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (enqueuePerPeerRx (Pure.pure () : WG.M Unit) id .dead) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (rx_publish id .dead history) (fun pid =>
    preserves_bind (preserves_pure ()) (fun _ => peer_put (some pid) history))

theorem rx_admit (msg : List UInt8) (src : SkbSource) (ds : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keypairGetNull; exact frame_store history _ keypairGetNull_sameStore)
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact rx_enqueue _ history)
    | (rx_retention_head enqueuePerPeerRx; exact rx_dead _ history)
    | (rx_retention_head newRxSkb; unfold newRxSkb; exact skb _ history)
    | archive_poll_step history

theorem rx_entry (msg : List UInt8) (src : SkbSource) (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) (wgReceive msg src) := by
  unfold wgReceive packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,invariant,unsupported,queueDeviceWork]
  repeat' first
    | (rx_retention_head consumeData; exact rx_admit _ _ _ history)
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (StateInv history))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (StateInv history))
    | archive_poll_step history

theorem product_wg_stable (h : List TimestampReceipt) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : ProductInv h w) : ProductInv h v := by
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  have frontier : v.wg.peerCounter = w.wg.peerCounter := congrArg WGStoreView.peerCounter same
  apply state_retained hi
  · intro pid stamp found
    simpa only [freshnessAt,device] using found
  · rw [frontier]
    exact Nat.le_refl _

theorem multicast_native (family addr : Nat) (history : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv history w.wg) (Env.xmitMulticastLoop family addr) := by
  have native : Framing.Preserves (fun w : World => StateInv history w.wg)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (frame_store history _ (loopbackSend_kernel [] true))
  have ambient {α : Type} (a : AmbientM α) :
      Framing.Preserves (fun w : World => StateInv history w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  routing_tx_source [Env.xmitMulticastLoop] using [native,ambient]

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
