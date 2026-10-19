import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialWorkerFrames
import Leanux.Proofs.WG.HandshakeSecurity.StagingMaterialSource
import Leanux.Proofs.WG.TransmitSecurity.PacketOriginStagingFrames

/-! Native actor leaves for resident packet/key continuity. Key acquisition
and release may change reference counts or remove cells; survivor bindings
remain allocation-stamped and the numeric allocation frontier stays visible. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing
open Lifetimes Queues TransmitSecurity Responder Origins.Retaining

theorem store {action : WG.M α} (same : SameWGStore action) : Preserves (Inv h) action :=
  frame (same.of_factor (fun s => PacketOrigins.snapshot {dev := s.dev})
      PacketOrigins.snapshot (fun _ => rfl))
    (core_of_same (same.of_factor (fun s => pool {dev := s.dev}) pool (fun _ => rfl)))
    (fun _ => lower_frame (same.of_factor (fun s => cursor {dev := s.dev}) cursor (fun _ => rfl)))

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

theorem modify_device (f : Device → Device)
    (epoch : ∀ d, (f d).ifindex = d.ifindex) (packets : ∀ d, (f d).txSkbs = d.txSkbs)
    (keys : ∀ d, (f d).keypairs = d.keypairs)
    (frontier : ∀ d, (f d).nextKeypairId = d.nextKeypairId) : Preserves (Inv h) (modifyDev f) := by
  apply frame (PacketOrigins.modify f epoch packets)
  · exact core_of_same (pool_of_material (modifyDev_material f (fun d => Prod.ext (epoch d) (keys d))))
  · intro bound
    apply lower_frame
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    simp only [cursor,Option.map_map,Function.comp_def,frontier]

theorem set_peer (pid : PeerId) (peer : Peer) : Preserves (Inv h) (setPeer pid peer) :=
  modify_device _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)

theorem peer_get (pid : PeerId) : Preserves (Inv h) (peerGet pid) :=
  frame (PacketOrigins.snapshot_pair (PacketOrigins.epoch_ring (TxRing.peerGet_frame pid))
      (PacketMaterial.of_packets (TxDisposition.peerGet_packets pid)))
    (core_of_same (pool_of_material (peerGet_material pid)))
    (fun _ => lower_metadata (peerGet_metadata pid))

theorem peer_put (pid : Option PeerId) : Preserves (Inv h) (peerPut pid) :=
  frame (PacketOrigins.snapshot_pair (PacketOrigins.epoch_ring (TxRing.peerPut_frame pid))
      (PacketMaterial.of_packets (TxDisposition.peerPut_packets pid)))
    (core_of_same (pool_of_material (peerPut_material pid)))
    (fun _ => lower_metadata (peerPut_metadata pid))

theorem key_put (kid : Option KeypairId) (now : Bool) : Preserves (Inv h) (keypairPut kid now) :=
  frame (PacketOrigins.snapshot_pair (PacketOrigins.epoch_ring (TxRing.keypairPut_frame kid now))
      (PacketMaterial.of_packets (TxDisposition.keyPut_packets kid now)))
    (keypairPut_core kid now)
    (fun _ => lower_metadata ((keypairPut_rest kid now).factor (fun rest => rest.2.2)))

theorem lower_key_get (kid : Option KeypairId) : Preserves (Lower bound) (keypairGet kid) := by
  unfold keypairGet refcountIncNotZero
  simp (config := {zeta := false}) only [branch,branchCmp,unsupported]
  repeat' material_cursor_step

theorem key_get (kid : Option KeypairId) : Preserves (Inv h) (keypairGet kid) :=
  frame (PacketOrigins.snapshot_wire (RetirementSecurity.keyGet_cryptWire kid))
    (core_of_same (keypairGet_core kid)) (fun _ => lower_key_get kid)

theorem reservation (kid : KeypairId) : Preserves (Inv h) (Nonce.reserveNative kid) := by
  apply frame
  · unfold Nonce.reserveNative
    have getter : SameView PacketOrigins.snapshot (getKeypair kid) := by
      apply (ProjectedAction.iff_run_ambient _ _ _).mpr
      intro w a key v b run
      exact congrArg PacketOrigins.snapshot (KeyTimes.getKeypair_return kid w v key a b run).1
    exact getter.bind (fun key => (PacketOrigins.modify
      (fun d => {d with keypairs := d.keypairs.insert kid {key with sendingCounter := key.sendingCounter + 1}})
      (fun _ => rfl) (fun _ => rfl)).bind (fun _ => SameView.pure _ _))
  · exact core_of_same (StagingMaterial.reserve_pool kid)
  · intro bound
    unfold Nonce.reserveNative
    exact preserves_bind (lower_key_read kid) (fun _ =>
      preserves_bind (lower_metadata (setKeypair_metadata _ _)) (fun _ => preserves_pure _))

theorem selection (pid : PeerId) : Preserves (Inv h) (selectionPrefix pid) := by
  unfold selectionPrefix
  apply preserves_bind (read_peer pid)
  intro peer
  apply preserves_bind (hoare_liftAmbient (AmbientM.branch .stagedEmpty peer.staged.isEmpty) _)
  intro empty
  split
  · exact preserves_pure _
  · exact preserves_bind (set_peer pid _) (fun _ =>
      preserves_bind (key_get peer.keypairCurrent) (fun _ => preserves_pure _))

theorem write_packet (id : SkbId) (f : DataPacket → DataPacket)
    (same : ∀ packet, PacketMaterial.material (f packet) = PacketMaterial.material packet) :
    Preserves (Inv h) (setTxSkb id f) :=
  frame (PacketOrigins.snapshot_pair (PacketOrigins.skb_epoch _) (PacketMaterial.set_tx id f same))
    (core_of_same ((skb_allocation_view _).factor Prod.fst))
    (fun _ => lower_frame ((skb_allocation_view _).factor (fun fields => fields.2.1)))

theorem free_packet (id : SkbId) : Preserves (Inv h) (freeTxSkb id) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  have fields := (ProjectedAction.iff_run_ambient _ _ _).mp
    (skb_allocation_view (SkbStore.freeTx id)) w a result v b run
  have cores := congrArg Prod.fst fields
  have frontier := congrArg (fun fields => fields.2.1) fields
  have epochs := congrArg (fun fields => fields.2.2) fields
  dsimp only [allocationView] at cores frontier epochs
  apply before.retains
  · have packets := (hoare_iff_run_ambient _ _ _).mp
      (TxDisposition.free_packet_wp id (TxDisposition.txPackets w)) w a result v b rfl run
    intro generation atEpoch target value resident
    refine ⟨epochs ▸ atEpoch,?_⟩
    unfold PacketMaterial.view at resident ⊢
    rw [packets] at resident
    by_cases same : id = target
    · simp only [same,ite_true,Option.map_none] at resident
      cases resident
    · simpa only [same,ite_false] using resident
  · intro d e hd he
    have same : e.nextKeypairId = d.nextKeypairId := by
      simpa only [cursor,hd,he,Option.map_some,Option.some.injEq] using frontier
    exact Nat.le_of_eq same.symm
  · intro _ _ slot _ core resident
    rw [←cores]
    exact resident

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial.NativeFrames
