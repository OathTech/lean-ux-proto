import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionDeferred
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverTrafficFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity

/-- Native index lookup frame from `Noise.PendingReception.indexLookup_pending_frame`
at C2 pin `7ff94e48c2a3323ef29e6fb62f82a4a64d43f218`. It asserts only the
one-call pending allocation projection, independently of history. -/
structure H1IngressFrames : Prop where
  lookup : ∀ kinds index, SameView view (indexLookup kinds index)

theorem Carrier.index_lookup (frames : H1IngressFrames) (kinds : List IndexKind)
    (index : Nat) (confirmed : List Nat) : Preserves (Carrier confirmed) (indexLookup kinds index) :=
  Carrier.join confirmed (ConfiguredIdentity.indexLookup_preserves kinds index)
    (CurrentSlots.indexLookup_preserves kinds index) (frame_preserves (frames.lookup kinds index) confirmed)

theorem Carrier.rx_enqueue (id : SkbId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (enqueuePerDeviceAndPeerRx id) :=
  Carrier.from_frame (Responder.DriverCuts.carrier_rx_enqueue id)
    (frame (CurrentSlots.enqueuePerDeviceAndPeerRx_fields id)
      (Keypairs.WGMore.enqueuePerDeviceAndPeerRx_sameSnapshot id)) confirmed

theorem Carrier.rx_dead (id : SkbId) (confirmed : List Nat) :
    Preserves (Carrier confirmed) (enqueuePerPeerRx (Pure.pure () : WG.M Unit) id .dead) := by
  rw [PublicationFrontier.enqueuePerPeerRx_factor]
  exact preserves_bind (Carrier.rx_publish id .dead confirmed) (fun pid =>
    preserves_bind (preserves_pure ()) (fun _ => Carrier.peer_put confirmed (some pid)))

theorem Carrier.update_bind (pid : PeerId) (f : Peer → Peer) (tail : Unit → WG.M α)
    (configured : ∀ p, ConfiguredIdentity.cell (f p) = ConfiguredIdentity.cell p)
    (slots : ∀ p, CurrentSlots.slotCell (f p) = CurrentSlots.slotCell p)
    (confirmed : List Nat) (next : ∀ x, Preserves (Carrier confirmed) (tail x)) :
    Preserves (Carrier confirmed) (getPeer pid >>= fun p => setPeer pid (f p) >>= tail) := by
  simpa only [bind_assoc] using preserves_bind
    (Carrier.modify_peer confirmed pid f slots configured) next

macro "pending_carrier_ingress_step " frames:term "," confirmed:term : tactic => `(tactic| first
  | (receive_update_head Bind.bind
     apply Carrier.update_bind
     · intro p; rfl
     · intro p; rfl
     intro x)
  | (rx_retention_head indexLookup; exact Carrier.index_lookup $frames _ _ $confirmed)
  | (rx_retention_head getDev; exact Carrier.store $confirmed getDev_sameWGStore)
  | (rx_retention_head ite; apply Carrier.conditional $confirmed)
  | pending_carrier_poll_step (), $confirmed)

theorem Carrier.rx_admit (frames : H1IngressFrames) (msg : List UInt8) (src : SkbSource)
    (ds : Nat) (confirmed : List Nat) : Preserves (Carrier confirmed) (consumeData msg src ds) := by
  unfold consumeData WG.orM
  simp (config := {zeta := false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head keypairGet; exact Carrier.key_get confirmed _)
    | (rx_retention_head keypairGetNull; exact Carrier.store confirmed keypairGetNull_sameStore)
    | (rx_retention_head enqueuePerDeviceAndPeerRx; exact Carrier.rx_enqueue _ confirmed)
    | (rx_retention_head enqueuePerPeerRx; exact Carrier.rx_dead _ confirmed)
    | (rx_retention_head newRxSkb; unfold newRxSkb; exact Carrier.skb confirmed _)
    | pending_carrier_ingress_step frames, confirmed

theorem Carrier.rx_entry (frames : H1IngressFrames) (msg : List UInt8) (src : SkbSource)
    (confirmed : List Nat) : Preserves (Carrier confirmed) (wgReceive msg src) := by
  unfold wgReceive packetReceive cpumaskNextOnline
  simp (config := {zeta := false}) only [branch,invariant,unsupported,queueDeviceWork]
  repeat' first
    | (rx_retention_head consumeData; exact Carrier.rx_admit frames _ _ _ confirmed)
    | (rx_retention_head prepareSkbHeader; exact (prepareSkbHeader_sameWGWorld _).wp (Carrier confirmed))
    | (rx_retention_head ipTunnelGetDsfield; exact (ipTunnelGetDsfield_sameWGWorld _ _).wp (Carrier confirmed))
    | pending_carrier_ingress_step frames, confirmed

theorem product_wg_stable (h : List Event) (w v : World)
    (same : wgStoreView v.wg = wgStoreView w.wg) (hi : ProductInv h w) : ProductInv h v := by
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  have counter : v.wg.keypairCounter = w.wg.keypairCounter := congrArg WGStoreView.keypairCounter same
  refine ⟨?_,CurrentSlots.fields_transport hi.2.1 ?_,hi.2.2.retained ?_⟩
  · intro s hs
    apply hi.1 s
    simpa only [ConfiguredIdentity.view,device] using hs
  · unfold CurrentSlots.fields RxCredits.keyWords
    rw [device]
  · have keys : keypairResidents v.wg = keypairResidents w.wg := by
      funext kid
      simp only [keypairResidents,device]
    have projection : view v.wg = view w.wg := by
      simp only [view,nextSlot,keys,device,counter]
    rw [projection]
    exact Retained.refl _

theorem Carrier.multicast (family addr : Nat) (confirmed : List Nat) :
    Preserves (fun w : World => Carrier confirmed w.wg) (Env.xmitMulticastLoop family addr) := by
  have native : Preserves (fun w : World => Carrier confirmed w.wg)
      (monadLift (loopbackSend [] true) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (Carrier.store confirmed (loopbackSend_kernel [] true))
  have ambient {α : Type} (a : AmbientM α) :
      Preserves (fun w : World => Carrier confirmed w.wg) (monadLift a : Leanux.M α) :=
    productAmbient_spec a _ (fun _ _ hi => hi)
  routing_tx_source [Env.xmitMulticastLoop] using [native,ambient]

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
