import Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
import Leanux.Proofs.WG.RetirementSecurity.TxCryptWireFrames

/-! Frames for allocation provenance. Backward retention permits disposal;
it never claims that a reference or a packet survives a final release. -/
namespace Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TxDisposition

def snapshot (w : WGWorld) := (epoch w, PacketMaterial.view w)

def Retains (before after : WGWorld) : Prop :=
  ∀ generation, epoch after = some generation → ∀ id value,
    PacketMaterial.view after id = some value →
      epoch before = some generation ∧ PacketMaterial.view before id = some value

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
  intro generation atEpoch id packet resident
  have cell : PacketMaterial.view v id = some (PacketMaterial.material packet) := by
    simp only [PacketMaterial.view,resident,Option.map_some]
  obtain ⟨oldEpoch,oldCell⟩ := frame generation atEpoch id _ cell
  obtain ⟨old,resident,material⟩ := Option.map_eq_some_iff.mp oldCell
  rw [← material]
  exact before generation oldEpoch id old resident

theorem frame {action : WG.M α} (same : SameView snapshot action) : Preserves (Inv h) action := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.retains (.of_snapshot ((ProjectedAction.iff_run_ambient _ _ _).mp same w a result v b run))

theorem snapshot_pair {action : WG.M α} (epochs : SameView epoch action)
    (packets : SameView PacketMaterial.view action) : SameView snapshot action := by
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  exact Prod.ext ((ProjectedAction.iff_run_ambient _ _ _).mp epochs w a result v b run)
    ((ProjectedAction.iff_run_ambient _ _ _).mp packets w a result v b run)

theorem epoch_ring {action : WG.M α} (same : SameView TxRing.nativeCell action) :
    SameView epoch action := by
  exact same.of_factor (fun cell => cell.map Prod.fst) epoch
    (fun w => by simp only [TxRing.nativeCell,epoch,Option.map_map,Function.comp_def])

theorem snapshot_wire {action : WG.M α} (same : SameView RetirementSecurity.txCryptWire action) :
    SameView snapshot action :=
  snapshot_pair (epoch_ring (same.factor Prod.fst)) (PacketMaterial.of_packets (same.factor Prod.snd))

theorem modify (f : Device → Device) (epochs : ∀ d, (f d).ifindex = d.ifindex)
    (packets : ∀ d, (f d).txSkbs = d.txSkbs) : SameView snapshot (modifyDev f) := by
  apply snapshot_pair
  · apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a result v b run
    cases run
    simp [epoch,Option.map_map,Function.comp_def,epochs]
  · exact PacketMaterial.modify_device f packets

theorem skb_epoch (action : SkbM α) : SameView epoch (liftSkb action) := by
  intro initial
  apply hoare_liftSkb
  intro w d store before device
  simpa only [epoch,device,Option.map_some] using before

theorem write_bytes (id : SkbId) (bytes : List UInt8) :
    Preserves (Inv h) (setTxSkb id (fun p => {p with bytes})) :=
  frame (snapshot_pair (skb_epoch _) (PacketMaterial.set_tx id _ (fun _ => rfl)))

theorem free_list (item : List SkbId) : Preserves (Inv h) (freeList item) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  apply before.retains
  have packets := (hoare_iff_run_ambient _ _ _).mp (freeList_wp item (txPackets w)) w a result v b rfl run
  have epochs := (ProjectedAction.iff_run_ambient _ _ _).mp
    (epoch_ring (RetirementSecurity.free_list_ring item)) w a result v b run
  intro generation atEpoch id value resident
  refine ⟨epochs ▸ atEpoch,?_⟩
  unfold PacketMaterial.view at resident ⊢
  rw [packets] at resident
  by_cases member : id ∈ item
  · simp only [member,ite_true,Option.map_none] at resident
    cases resident
  · simpa only [member,ite_false] using resident

theorem publish (item : List SkbId) (state : PacketState) :
    Preserves (Inv h) (enqueuePerPeerTx item state) :=
  frame (snapshot_pair (epoch_ring (TxRing.enqueuePeer_frame item state)) (PacketMaterial.publish item state))

theorem encrypt_packet_epoch (key : KeypairId) (pkt : DataPacket) :
    SameView (fun w : World => epoch w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  intro initial
  let P := fun w : World => epoch w.wg = initial
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (fun w => epoch w = initial))
  have checksumSpec (p : Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) :=
    PublicationPoll.native_product _ _ ((epoch_ring (TxRing.getKeypair_frame key)).wp (· = initial))
  change Preserves P _
  routing_tx_source [encryptPacket] using [padding,checksumSpec,keySpec,ambient]

theorem encrypt_tail_epoch (item : Option (List SkbId)) :
    SameView (fun w : World => epoch w.wg) (RxWorkers.encryptStepTailSource item) := by
  intro initial
  let Q := fun w : WGWorld => epoch w = initial
  let P := fun w : World => Q w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have readNative (id : SkbId) : Preserves Q (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a packet v b before run
    exact (Packets.getTxSkb_current id w v packet a b run).1 ▸ before
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product Q _ (readNative id)
  have writeNative (id : SkbId) (bytes : List UInt8) :
      Preserves Q (setTxSkb id (fun p => {p with bytes})) := by
    unfold setTxSkb
    apply hoare_liftSkb
    intro w d store before device
    simpa only [Q,epoch,device,Option.map_some] using before
  have write (id : SkbId) (bytes : List UInt8) :
      Preserves P (monadLift (setTxSkb id (fun p => {p with bytes})) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (writeNative id bytes)
  have publish (batch : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx batch state) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ ((epoch_ring (TxRing.enqueuePeer_frame batch state)).wp (· = initial))
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := (encrypt_packet_epoch key pkt).wp (· = initial)
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]

theorem encrypt_tail (item : Option (List SkbId)) :
    Preserves (fun w : World => Inv h w.wg) (RxWorkers.encryptStepTailSource item) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  apply before.retains
  have packets := (ProjectedAction.iff_run _ _ _).mp (PacketMaterial.encrypt_tail item) w result v run
  have epochs := (ProjectedAction.iff_run _ _ _).mp (encrypt_tail_epoch item) w result v run
  exact Retains.of_snapshot (Prod.ext epochs packets)

theorem encrypt_packet (key : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World => Inv h w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact before.retains (.of_snapshot (Prod.ext
    ((ProjectedAction.iff_run _ _ _).mp (encrypt_packet_epoch key pkt) w result v run)
    ((ProjectedAction.iff_run _ _ _).mp (PacketMaterial.encrypt_packet key pkt) w result v run)))

end Leanux.Proofs.WG.TransmitSecurity.PacketOrigins
