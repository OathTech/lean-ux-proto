import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialStack
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDecryptFrames

/-! Native crypt and TX-completion frames for the resident material carrier.
RX validity writes and TX disposal retain the immutable core of survivors. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder Origins.Retaining
set_option maxHeartbeats 600000

theorem fresh_core (pid : PeerId) : SameView pool (keepKeyFresh pid) := by
  intro initial
  unfold keepKeyFresh
  material_lower
  repeat' first
    | (index_material_head sendQueuedHandshakeInitiation; exact (queued_core _ _).wp (fun p => p = initial))
    | core_traffic (fun p => p = initial)

theorem data_done_core (pid : PeerId) (item : List SkbId) : SameView pool (createDataDone pid item) := by
  intro initial
  unfold createDataDone
  material_lower
  repeat' first
    | (index_material_head timersTraversal; exact (pool_of_material (timersTraversal_material _)).wp (fun p => p = initial))
    | (index_material_head timersAnyAuthenticatedPacketSent; exact (pool_of_material (timersAnyAuthenticatedPacketSent_material _)).wp (fun p => p = initial))
    | (index_material_head sendSkbToPeer; exact (pool_of_material (sendSkbToPeer_material _ _ _)).wp (fun p => p = initial))
    | (index_material_head timersDataSent; exact (pool_of_material (timersDataSent_material _)).wp (fun p => p = initial))
    | (index_material_head keepKeyFresh; exact (fresh_core _).wp (fun p => p = initial))
    | core_traffic (fun p => p = initial)

theorem data_done (pid : PeerId) (item : List SkbId) : Preserves (Inv h) (createDataDone pid item) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.createDataDone_cryptWire pid item))
    (core_of_same (data_done_core pid item))
    (fun _ => lower_owner_geometry
      ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationTransmit.«0».Leanux.Proofs.WG.PublicationJoint.complete_geometry) pid item))

theorem transmit (pid : PeerId) : Preserves (Inv h) (txStep pid) := by
  unfold txStep WG.andM
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head createDataDone; exact data_done _ _)
    | resident_poll_frame

theorem poll : Preserves (Inv h) TxRing.pollSource := by
  unfold TxRing.pollSource
  repeat' resident_staging_step

theorem lower_decrypt (pkt : RxPacket) : Preserves (Lower bound) (decryptPacket pkt) := by
  have reject (key : Keypair) : Preserves (Lower bound) (KeyTimes.receiveReject key) :=
    lower_frame ((decryptKeyReject_sameWGStore key).of_factor
      (fun s : WGStoreView => cursor {dev := s.dev}) cursor (fun _ => rfl))
  rw [KeyTimes.decryptPacket_factor]
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .decNoKeypair false) _)
  intro noKey
  cases noKey with
  | true => exact preserves_pure none
  | false =>
    apply preserves_bind (lower_key_read pkt.keypair)
    intro key
    apply preserves_bind (reject key)
    intro rejected
    cases rejected with
    | true =>
      simp only [ite_true]
      repeat' resident_lower_step
    | false => exact lower_frame ((Origins.receiveTail_sameWGWorld pkt key).factor cursor)

theorem decrypt (pkt : RxPacket) : Preserves (Inv h) (decryptPacket pkt) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.OccurrenceDecrypt.packet_wire pkt))
    (core_of_same (decrypt_core pkt)) (fun _ => lower_decrypt pkt)

theorem rx_publish (id : SkbId) (state : PacketState) : Preserves (Inv h) (RxWorkers.publishSource id state) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.OccurrenceDecrypt.publish_wire id state))
    (core_of_same (publish_core id state)) (fun _ => lower_slot_fields (CurrentSlots.publish_fields id state))

theorem write_rx (id : SkbId) (f : RxPacket → RxPacket) : Preserves (Inv h) (setRxSkb id f) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.ReceiveOccurrences.set_rx_wire id f))
    (core_of_same ((skb_allocation_view (SkbStore.setRx id f)).factor Prod.fst))
    (fun _ => lower_frame ((skb_allocation_view (SkbStore.setRx id f)).factor (fun fields => fields.2.1)))

theorem prepare_worker : Preserves (Inv h) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact decrypt _)
    | (rx_retention_head RxWorkers.publishSource; exact rx_publish _ _)
    | (rx_retention_head setRxSkb; exact write_rx _ _)
    | resident_poll_frame

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
