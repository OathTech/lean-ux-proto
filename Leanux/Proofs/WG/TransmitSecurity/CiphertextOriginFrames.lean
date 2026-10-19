import Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
import Leanux.Proofs.WG.RetirementSecurity.TxCryptWireFrames

/-! Frames for resident ciphertext provenance. Backward retention permits disposal;
it never claims that a reference or a packet survives a final release. -/
namespace Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition


def snapshot (w : WGWorld) := (PacketOrigins.epoch w, PacketPayload.view w)

def Retains (before after : WGWorld) : Prop :=
  ∀ generation, PacketOrigins.epoch after = some generation → ∀ id value,
    PacketPayload.view after id = some value →
      PacketOrigins.epoch before = some generation ∧ PacketPayload.view before id = some value

theorem Retains.refl (w : WGWorld) : Retains w w := fun _ e _ _ p => ⟨e,p⟩

theorem Retains.trans (first : Retains a b) (second : Retains b c) : Retains a c := by
  intro generation e id value p
  obtain ⟨e,p⟩ := second generation e id value p
  exact first generation e id value p

theorem Retains.of_snapshot (same : snapshot after = snapshot before) : Retains before after := by
  obtain ⟨epochs,packets⟩ := Prod.mk.inj same
  intro generation e id value p
  exact ⟨epochs ▸ e, by rw [← packets]; exact p⟩

theorem Inv.retains (before : Inv h w) (frame : Retains w v) : Inv h v := by
  intro generation atEpoch id packet resident nonempty
  have cell : PacketPayload.view v id = some (PacketPayload.material packet) := by
    simp only [PacketPayload.view,resident,Option.map_some]
  obtain ⟨oldEpoch,oldCell⟩ := frame generation atEpoch id _ cell
  obtain ⟨old,resident,material⟩ := Option.map_eq_some_iff.mp oldCell
  have bytes : old.bytes = packet.bytes := by
    simpa only [PacketPayload.material] using congrArg DataPacket.bytes material
  rw [← material]
  exact before generation oldEpoch id old resident (bytes ▸ nonempty)

theorem frame {action : WG.M α} (same : SameView snapshot action) : Preserves (Inv h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.retains (.of_snapshot ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run))

theorem snapshot_pair {action : WG.M α} (epochs : SameView PacketOrigins.epoch action)
    (packets : SameView PacketPayload.view action) : SameView snapshot action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact Prod.ext ((ProjectedAction.iff_run_ambient _ _ _).mp epochs w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp packets w a result v b run)

theorem epoch_ring {action : WG.M α} (same : SameView TxRing.nativeCell action) :
    SameView PacketOrigins.epoch action := by
  exact same.of_factor (fun cell => cell.map Prod.fst) PacketOrigins.epoch
    (fun w => by simp only [TxRing.nativeCell,PacketOrigins.epoch,Option.map_map,Function.comp_def])

theorem snapshot_wire {action : WG.M α} (same : SameView RetirementSecurity.txCryptWire action) :
    SameView snapshot action :=
  snapshot_pair (epoch_ring (same.factor Prod.fst)) (PacketPayload.of_packets (same.factor Prod.snd))

theorem modify (f : Device → Device) (epochs : ∀ d, (f d).ifindex = d.ifindex)
    (packets : ∀ d, (f d).txSkbs = d.txSkbs) : SameView snapshot (modifyDev f) := by
  apply snapshot_pair
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    simp [PacketOrigins.epoch,Option.map_map,Function.comp_def,epochs]
  · exact PacketPayload.modify_device f packets

theorem skb_epoch (action : SkbM α) : SameView PacketOrigins.epoch (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d store before device
  simpa only [PacketOrigins.epoch,device,Option.map_some] using before

theorem free_list (item : List SkbId) : Preserves (Inv h) (freeList item) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  apply before.retains
  have packets := (hoare_iff_run_ambient _ _ _).mp (freeList_wp item (txPackets w)) w a result v b rfl run
  have epochs := (ProjectedAction.iff_run_ambient _ _ _).mp
    (epoch_ring (RetirementSecurity.free_list_ring item)) w a result v b run
  intro generation atEpoch id value resident
  refine ⟨epochs ▸ atEpoch,?_⟩
  unfold PacketPayload.view at resident ⊢
  rw [packets] at resident
  by_cases member : id ∈ item
  · simp only [member,ite_true,Option.map_none] at resident
    cases resident
  · simpa only [member,ite_false] using resident

theorem publish (item : List SkbId) (state : PacketState) :
    Preserves (Inv h) (enqueuePerPeerTx item state) :=
  frame (snapshot_pair (epoch_ring (TxRing.enqueuePeer_frame item state)) (PacketPayload.publish item state))

theorem encrypt_packet_epoch (key : KeypairId) (pkt : DataPacket) :
    SameView (fun w : World => PacketOrigins.epoch w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  intro initial
  let P := fun w : World => PacketOrigins.epoch w.wg = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (fun w => PacketOrigins.epoch w = initial))
  have checksumSpec (p : Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) :=
    PublicationPoll.native_product _ _ ((epoch_ring (TxRing.getKeypair_frame key)).wp (· = initial))
  change Preserves P _
  routing_tx_source [encryptPacket] using [padding,checksumSpec,keySpec,ambient]

theorem encrypt_packet (key : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World => Inv h w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact before.retains (.of_snapshot (Prod.ext
    ((ProjectedAction.iff_run _ _ _).mp (encrypt_packet_epoch key pkt) w result v run)
    ((ProjectedAction.iff_run _ _ _).mp (PacketPayload.encrypt_packet key pkt) w result v run)))

end Leanux.Proofs.WG.TransmitSecurity.CiphertextOrigins
