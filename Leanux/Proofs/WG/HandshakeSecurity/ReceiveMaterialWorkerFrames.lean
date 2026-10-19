import Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterialFrontFrames
import Leanux.Proofs.WG.AuthenticatedEffects.TransportWorkerFrames

/-! Native TX crypt and completion workers preserve every surviving RX
allocation certificate, independently of their packet and reference accounts. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues AuthenticatedEffects Responder Origins.Retaining Std.Do
set_option maxHeartbeats 600000

theorem bounded_tx_read (id : SkbId) : Preserves (Bounded h) (getTxSkb id) :=
  bounded_frame (TransportCarrier.getTxSkb_rx id)
    (ResidentMaterial.core_of_same ((ResidentMaterial.skb_allocation_view (SkbStore.getTx id)).factor Prod.fst))
    (fun _ => ResidentMaterial.lower_frame
      ((ResidentMaterial.skb_allocation_view (SkbStore.getTx id)).factor (fun fields => fields.2.1)))

theorem bounded_tx_write (id : SkbId) (f : DataPacket → DataPacket) : Preserves (Bounded h) (setTxSkb id f) :=
  bounded_frame ((RxCredits.setTx_protect id f).factor (fun v => v.2.1))
    (ResidentMaterial.core_of_same ((ResidentMaterial.skb_allocation_view (SkbStore.setTx id f)).factor Prod.fst))
    (fun _ => ResidentMaterial.lower_frame
      ((ResidentMaterial.skb_allocation_view (SkbStore.setTx id f)).factor (fun fields => fields.2.1)))

theorem bounded_tx_free (id : SkbId) : Preserves (Bounded h) (freeTxSkb id) :=
  bounded_frame ((RxCredits.freeTx_protect id).factor (fun v => v.2.1))
    (ResidentMaterial.core_of_same ((ResidentMaterial.skb_allocation_view (SkbStore.freeTx id)).factor Prod.fst))
    (fun _ => ResidentMaterial.lower_frame
      ((ResidentMaterial.skb_allocation_view (SkbStore.freeTx id)).factor (fun fields => fields.2.1)))

theorem bounded_publication (item : List SkbId) (state : PacketState) :
    Preserves (Bounded h) (enqueuePerPeerTx item state) :=
  bounded_frame
    (((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.enqueuePeer_geometry) item state).factor Prod.snd)
    (ResidentMaterial.core_of_same (publication_core item state))
    (fun _ => ResidentMaterial.lower_publication item state)

theorem bounded_encrypt_packet (kid : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World => Bounded h w.wg) (encryptPacket Env.checksumHelp kid pkt) := by
  let P := fun w : World => Bounded h w.wg
  have effect {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (Bounded h))
  have checksum (p : Packet) : Preserves P (Env.checksumHelp p) := (checksumHelp_sameWorld p).wp P
  have read : Preserves P (monadLift (getKeypair kid) : Leanux.M Keypair) := by
    apply PublicationPoll.native_product
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a key v b hi run
    exact (KeyTimes.getKeypair_return kid w v key a b run).1 ▸ hi
  routing_tx_source [encryptPacket] using [padding,checksum,read,effect]

theorem bounded_encrypt_tail (item : Option (List SkbId)) :
    Preserves (fun w : World => Bounded h w.wg) (RxWorkers.encryptStepTailSource item) := by
  let P := fun w : World => Bounded h w.wg
  have effect {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product _ _ (bounded_tx_read id)
  have write (id : SkbId) (f : DataPacket → DataPacket) : Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (bounded_tx_write id f)
  have publish (items : List SkbId) (state : PacketState) : Preserves P
      (monadLift (enqueuePerPeerTx items state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (bounded_publication items state)
  have packet (kid : KeypairId) (pkt : DataPacket) : Preserves P (encryptPacket Env.checksumHelp kid pkt) :=
    bounded_encrypt_packet kid pkt
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,publish,packet,effect]

theorem bounded_data_done (pid : PeerId) (item : List SkbId) :
    Preserves (Bounded h) (createDataDone pid item) :=
  bounded_frame
    (((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTransmit.«0».Leanux.Proofs.WG.PublicationJoint.complete_geometry) pid item).factor Prod.snd)
    (ResidentMaterial.core_of_same (ResidentMaterial.NativeFrames.data_done_core pid item))
    (fun _ => ResidentMaterial.NativeFrames.lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTransmit.«0».Leanux.Proofs.WG.PublicationJoint.complete_geometry) pid item))

theorem bounded_transmit (pid : PeerId) : Preserves (Bounded h) (txStep pid) := by
  unfold txStep WG.andM
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head createDataDone; exact bounded_data_done _ _)
    | (rx_retention_head getTxSkb; exact bounded_tx_read _)
    | (rx_retention_head freeTxSkb; exact bounded_tx_free _)
    | (rx_retention_head PrevQueue.peek; exact bounded_store (prevQueuePeek_sameWGStore _))
    | (rx_retention_head List.forM; apply forM_preserves; intro id)
    | receive_bounded_native_step

theorem bounded_encrypt_poll : Preserves (Bounded h) TxRing.pollSource := by
  unfold TxRing.pollSource
  repeat' receive_bounded_native_step

end Leanux.Proofs.WG.HandshakeSecurity.ReceiveMaterial
