import Leanux.Proofs.WG.TransmitSecurity.PacketOriginFrames
import Leanux.Proofs.WG.RetirementSecurity.TxCryptStagingFrames

/-! Native staging and refusal frames for the allocation-origin carrier.
Queue publication may alter a head mark, and refusal may free a whole batch;
neither operation invents replacement packet material. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues Std.Do
open TxDisposition
set_option maxHeartbeats 600000

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Inv h) action :=
  frame (same.of_factor (fun s => snapshot {dev := s.dev}) snapshot (fun _ => rfl))

theorem read_peer (pid : PeerId) : Preserves (Inv h) (getPeer pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (Peers.getPeer_current pid w v result a b run).1 ▸ before

theorem read_key (kid : KeypairId) : Preserves (Inv h) (getKeypair kid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (KeyTimes.getKeypair_return kid w v result a b run).1 ▸ before

theorem read_packet (id : SkbId) : Preserves (Inv h) (getTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact (Packets.getTxSkb_current id w v result a b run).1 ▸ before

theorem peer_get (pid : PeerId) : Preserves (Inv h) (peerGet pid) :=
  frame (snapshot_pair (epoch_ring (TxRing.peerGet_frame pid)) (PacketMaterial.of_packets (peerGet_packets pid)))

theorem peer_put (pid : Option PeerId) : Preserves (Inv h) (peerPut pid) :=
  frame (snapshot_pair (epoch_ring (TxRing.peerPut_frame pid)) (PacketMaterial.of_packets (peerPut_packets pid)))

theorem key_put (kid : Option KeypairId) (now : Bool) : Preserves (Inv h) (keypairPut kid now) :=
  frame (snapshot_pair (epoch_ring (TxRing.keypairPut_frame kid now)) (PacketMaterial.of_packets (keyPut_packets kid now)))

theorem key_get (kid : Option KeypairId) : Preserves (Inv h) (keypairGet kid) :=
  frame (snapshot_wire (RetirementSecurity.keyGet_cryptWire kid))

theorem free_packet (id : SkbId) : Preserves (Inv h) (freeTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  apply before.retains
  have packets := (hoare_iff_run_ambient _ _ _).mp (free_packet_wp id (txPackets w)) w a result v b rfl run
  have epochs := (ProjectedAction.iff_run_ambient _ _ _).mp (skb_epoch (SkbStore.freeTx id)) w a result v b run
  intro generation atEpoch target value resident
  refine ⟨epochs ▸ atEpoch,?_⟩
  unfold PacketMaterial.view at resident ⊢
  rw [packets] at resident
  by_cases same : id = target
  · simp only [same,ite_true,Option.map_none] at resident; cases resident
  · simpa only [same,ite_false] using resident

theorem write_packet (id : SkbId) (f : DataPacket → DataPacket)
    (same : ∀ p, PacketMaterial.material (f p) = PacketMaterial.material p) :
    Preserves (Inv h) (setTxSkb id f) :=
  frame (snapshot_pair (skb_epoch _) (PacketMaterial.set_tx id f same))

macro "origin_staging_frame" : tactic => `(tactic| first
  | rxstack_preserves_join
  | (rx_retention_head getPeer; exact read_peer _)
  | (rx_retention_head getTxSkb; exact read_packet _)
  | (rx_retention_head getKeypair; exact read_key _)
  | (rx_retention_head getDev; exact store getDev_sameWGStore)
  | (rx_retention_head setPeer; exact frame (PacketOrigins.modify _ (fun _ => rfl) (fun _ => rfl)))
  | (rx_retention_head setKeypair; exact frame (PacketOrigins.modify _ (fun _ => rfl) (fun _ => rfl)))
  | (rx_retention_head setTxSkb; exact write_packet _ _ (fun _ => rfl))
  | (rx_retention_head freeTxSkb; exact free_packet _)
  | (rx_retention_head peerGet; exact peer_get _)
  | (rx_retention_head peerPut; exact peer_put _)
  | (rx_retention_head keypairGet; exact key_get _)
  | (rx_retention_head keypairPut; exact key_put _ _)
  | (rx_retention_head modifyDev; exact frame (PacketOrigins.modify _ (fun _ => rfl) (fun _ => rfl)))
  | (rx_retention_head IndexOwner.peerDeref; exact indexOwner_peerDeref_preserves _ _)
  | (rx_retention_head ForIn.forIn; apply list_view_spec id (Inv _); intro x b; change Preserves (Inv _) _)
  | (allocation_release_lift_from AmbientM; exact hoare_liftAmbient _ _)
  | (rx_retention_head get; exact hoare_consequence (hoare_get _) (fun _ h => h) (fun _ _ h => h.2))
  | rx_retention_step)

theorem reservation (kid : KeypairId) : Preserves (Inv h) (Nonce.reserveNative kid) := by
  unfold Nonce.reserveNative
  repeat' origin_staging_frame

theorem selection (pid : PeerId) : Preserves (Inv h) (HandshakeSecurity.Responder.selectionPrefix pid) := by
  unfold HandshakeSecurity.Responder.selectionPrefix
  simp only [branch]
  repeat' origin_staging_frame

theorem out (pid : PeerId) (packets : List Packet) (kid : Option KeypairId) (invalid : Bool) :
    Preserves (Inv h) (stagedOutNokey pid packets kid invalid) :=
  frame (snapshot_wire (RetirementSecurity.noKey_cryptWire pid packets kid invalid))

theorem enqueue (pid : PeerId) (items : List SkbId) : Preserves (Inv h) (enqueuePerDeviceAndPeer pid items) := by
  unfold enqueuePerDeviceAndPeer cpumaskNextOnlineFrom
  simp only [branch,invariant,queueDeviceWork]
  repeat' origin_staging_frame

theorem create (pid : PeerId) (items : List SkbId) : Preserves (Inv h) (createData pid items) := by
  unfold createData
  simp only [branch,invariant]
  repeat' first
    | (rx_retention_head enqueuePerDeviceAndPeer; exact enqueue _ _)
    | (rx_retention_head enqueuePerPeerTx; exact PacketOrigins.publish _ _)
    | origin_staging_frame

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins.NativeFrames
