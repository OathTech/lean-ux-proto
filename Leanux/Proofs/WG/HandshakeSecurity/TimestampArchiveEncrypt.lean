import Leanux.Proofs.WG.HandshakeSecurity.TimestampArchiveDecrypt

namespace Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues

theorem encrypt_frame (kid : KeypairId) (pkt : DataPacket) (history : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv history w.wg) (encryptPacket Env.checksumHelp kid pkt) := by
  let P := fun w : World => StateInv history w.wg
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Framing.Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (StateInv history))
  have checksum (p : WG.Packet) : Framing.Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have read : Framing.Preserves P (monadLift (getKeypair kid) : Leanux.M Keypair) :=
    PublicationPoll.native_product _ _ (read_key kid history)
  routing_tx_source [encryptPacket] using [padding,checksum,read,effect]

theorem encrypt_tail_frame (item : Option (List SkbId)) (history : List TimestampReceipt) :
    Framing.Preserves (fun w : World => StateInv history w.wg) (RxWorkers.encryptStepTailSource item) := by
  let P := fun w : World => StateInv history w.wg
  have effect {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have skb {α : Type} (a : SkbM α) : Framing.Preserves P (monadLift (liftSkb a) : Leanux.M α) :=
    PublicationPoll.native_product _ _ (TimestampArchive.skb a history)
  have encrypt (kid : KeypairId) (pkt : DataPacket) : Framing.Preserves P
      (encryptPacket Env.checksumHelp kid pkt) := encrypt_frame kid pkt history
  have publish (xs : List SkbId) (state : PacketState) : Framing.Preserves P
      (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (enqueue_peer xs state history)
  routing_tx_source [RxWorkers.encryptStepTailSource,getTxSkb,setTxSkb] using [skb,encrypt,publish,effect]

theorem encrypt_poll_frame (history : List TimestampReceipt) :
    Framing.Preserves (StateInv history) TxRing.pollSource := by
  unfold TxRing.pollSource
  apply preserves_bind (frame_store history _ getDev_sameWGStore)
  intro d
  apply preserves_bind (modify_device
    (fun dev => {dev with encryptQueue := d.encryptQueue.consume.2}) (fun _ => rfl) history)
  intro _
  exact preserves_pure _

theorem encrypt_tail (item : Option (List SkbId)) :
    ProductPreserves (TransmitSecurity.Driver.encryptTailObserved TimestampDriver.hooks item) :=
  workerIterPrefix_preserves _ _ (fun _ _ hi => hi.1)
    (product_lift _ (encrypt_tail_frame item)) (resched _ _)

theorem encrypt_iteration :
    ProductPreserves (TransmitSecurity.Driver.encryptIterObserved TimestampDriver.hooks) := by
  unfold TransmitSecurity.Driver.encryptIterObserved
  dsimp only [TimestampDriver.hooks]
  exact PrefixPreserves.bind (product_native _ encrypt_poll_frame) (fun _ =>
    PrefixPreserves.bind softirq (fun _ => encrypt_tail _))

end Leanux.Proofs.WG.HandshakeSecurity.TimestampArchive
