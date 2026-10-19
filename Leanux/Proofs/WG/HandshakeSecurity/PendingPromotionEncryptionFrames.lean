import Leanux.Proofs.WG.HandshakeSecurity.PendingPromotionTransmitFrames

namespace Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues Queues.RxCredits Origins

theorem Carrier.encrypt (kid : KeypairId) (pkt : DataPacket) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) (encryptPacket Env.checksumHelp kid pkt) := by
  let P := fun w : World => Carrier confirmed w.wg
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Framing.Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (Carrier confirmed))
  have checksum (p : WG.Packet) : Framing.Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have read : Framing.Preserves P (monadLift (getKeypair kid) : Leanux.M Keypair) :=
    PublicationPoll.native_product _ _ (Carrier.key_read kid confirmed)
  routing_tx_source [encryptPacket] using [padding,checksum,read,effect]

theorem Carrier.encrypt_tail (frames : H1PublicationFrame) (item : Option (List SkbId)) (confirmed : List Nat) :
    Framing.Preserves (fun w : World => Carrier confirmed w.wg) (RxWorkers.encryptStepTailSource item) := by
  let P := fun w : World => Carrier confirmed w.wg
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have skb {α : Type} (a : SkbM α) : Framing.Preserves P (monadLift (liftSkb a) : Leanux.M α) :=
    PublicationPoll.native_product _ _ (Carrier.skb confirmed a)
  have encrypt (kid : KeypairId) (pkt : DataPacket) : Framing.Preserves P
      (encryptPacket Env.checksumHelp kid pkt) := Carrier.encrypt kid pkt confirmed
  have publish (xs : List SkbId) (state : PacketState) : Framing.Preserves P
      (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (Carrier.publication frames xs state confirmed)
  routing_tx_source [RxWorkers.encryptStepTailSource,getTxSkb,setTxSkb] using [skb,encrypt,publish,effect]

theorem Carrier.encrypt_poll (confirmed : List Nat) :
    Framing.Preserves (Carrier confirmed) TxRing.pollSource := by
  unfold TxRing.pollSource
  apply preserves_bind (Carrier.store confirmed getDev_sameWGStore)
  intro d
  apply preserves_bind (Carrier.modify_device
    (fun dev => {dev with encryptQueue := d.encryptQueue.consume.2})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) confirmed)
  intro _
  exact preserves_pure _

end Leanux.Proofs.WG.HandshakeSecurity.PendingPromotion
