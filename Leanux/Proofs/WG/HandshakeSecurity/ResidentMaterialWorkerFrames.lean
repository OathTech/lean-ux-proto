import Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterialAllocation

/-! Native encryption-worker frames for the conditional allocation/material
carrier. These preserve existing bindings; they do not manufacture a key loan
or infer that a missing key survives retirement. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity Responder TxDisposition

theorem frame {action : WG.M α}
    (packets : SameView PacketOrigins.snapshot action)
    (keys : CoreRetains action)
    (frontier : ∀ bound, Preserves (Lower bound) action) : Preserves (Inv h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  apply before.retains
  · exact .of_snapshot ((ProjectedAction.iff_run_ambient _ _ _).mp packets w a result v b run)
  · intro d e hd he
    have entry : Lower d.nextKeypairId w := by
      intro front found
      have same : front = d.nextKeypairId := by simpa [cursor,hd] using found.symm
      exact same ▸ Nat.le_refl _
    exact (hoare_iff_run_ambient _ _ _).mp (frontier d.nextKeypairId) w a result v b entry run
      e.nextKeypairId (by simp [cursor,he])
  · intro _ _ slot _ core resident
    exact (ProjectedAction.iff_run_ambient _ _ _).mp keys w a result v b run slot core resident

theorem core_of_same {action : WG.M α} (same : SameView pool action) : CoreRetains action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [(ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run]
  exact Responder.Retains.refl _

theorem write_bytes (id : SkbId) (bytes : List UInt8) :
    Preserves (Inv h) (setTxSkb id (fun p => {p with bytes})) := by
  apply frame
  · exact PacketOrigins.snapshot_pair (PacketOrigins.skb_epoch _)
      (PacketMaterial.set_tx id _ (fun _ => rfl))
  · exact core_of_same ((skb_allocation_view _).factor Prod.fst)
  · intro bound
    exact lower_frame ((skb_allocation_view _).factor (fun fields => fields.2.1))

theorem lower_cpu (pid : PeerId) : Preserves (Lower bound) (cpumaskChooseOnline pid) := by
  unfold cpumaskChooseOnline
  simp (config := {zeta := false}) only [branch,Std.Legacy.Range.forIn_eq_forIn_range']
  repeat' first
    | (allocation_release_head ForIn.forIn
       apply list_view_spec cursor (fun cell => ∀ front, cell = some front → bound ≤ front)
       intro x acc
       change Preserves (Lower bound) _)
    | material_cursor_step

theorem lower_publication (item : List SkbId) (state : PacketState) :
    Preserves (Lower bound) (enqueuePerPeerTx item state) := by
  unfold enqueuePerPeerTx
  simp (config := {zeta := false}) only [peekQueuedUnit,recordQueued]
  repeat' first
    | (allocation_release_head getTxSkb
       apply (hoare_iff_run_ambient _ _ _).mpr
       intro w a packet v b before run
       exact (Packets.getTxSkb_current _ w v packet a b run).1 ▸ before)
    | (allocation_release_head setTxSkb
       exact lower_frame ((skb_allocation_view _).factor (fun fields => fields.2.1)))
    | (allocation_release_head getDev
       exact lower_frame (getDev_sameWGStore.of_factor
         (fun store : WGStoreView => store.dev.map (·.nextKeypairId)) cursor (fun _ => rfl)))
    | (allocation_release_head modifyDev; exact lower_metadata (metadata_modifyDev _ (fun _ => rfl)))
    | (allocation_release_head cpumaskChooseOnline; exact lower_cpu _)
    | (allocation_release_head peerGet; exact lower_metadata (peerGet_metadata _))
    | (allocation_release_head peerPut; exact lower_metadata (peerPut_metadata _))
    | material_cursor_step

theorem publish (item : List SkbId) (state : PacketState) :
    Preserves (Inv h) (enqueuePerPeerTx item state) :=
  frame (PacketOrigins.snapshot_pair
    (PacketOrigins.epoch_ring (TxRing.enqueuePeer_frame item state)) (PacketMaterial.publish item state))
    (core_of_same (publication_core item state)) (fun _ => lower_publication item state)

theorem encrypt_packet (key : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World => Inv h w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  let P := fun w : World => Inv h w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (Inv h))
  have checksumSpec (p : WG.Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) := by
    apply PublicationPoll.native_product
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi run
    exact (KeyTimes.getKeypair_return key w v k a b run).1 ▸ hi
  routing_tx_source [encryptPacket] using [padding,checksumSpec,keySpec,ambient]

end Leanux.Proofs.WG.HandshakeSecurity.ResidentMaterial
