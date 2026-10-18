import Leanux.Proofs.WG.RetirementSecurity.TxCryptAdmission

/-! The selected native encryption continuation retains exact key holders
and physical packet ownership. Cryptographic computation reads the store;
byte writes and publication update existing cells without adding references. -/
namespace Leanux.Proofs.WG.RetirementSecurity
open Leanux Leanux.WG Leanux.Proofs.Framing Lifetimes Queues

theorem encrypt_packet_store (key : KeypairId) (pkt : DataPacket) :
    SameView (fun w : World => wgStoreView w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  intro initial
  let P := fun w : World => wgStoreView w.wg = initial
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : Leanux.M α) :=
    productAmbient_spec action P (fun _ _ hi => hi)
  have native {α : Type} (action : WG.M α) (same : SameWGStore action) :
      Preserves P (monadLift action : Leanux.M α) :=
    (sameView_liftWG (fun w : World => wgStoreView w.wg) wgStoreView action same
      (fun _ _ _ hi => hi)).wp (· = initial)
  have padding := native (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu)
    ((calculateSkbPadding_sameWGWorld _ _).factor wgStoreView)
  have checksum (p : WG.Packet) : Preserves P (Env.checksumHelp p) := (checksumHelp_sameWorld p).wp P
  have getter : SameWGStore (getKeypair key) := by
    apply (ProjectedAction.iff_run_ambient _ _ _).mpr
    intro w a k v b run
    exact congrArg wgStoreView (KeyTimes.getKeypair_return key w v k a b run).1
  have keySpec := native (getKeypair key) getter
  change Preserves P _
  routing_tx_source [encryptPacket] using [padding,checksum,keySpec,ambient]

theorem HolderAccount.encrypt_packet (account : HolderAccount temporary w.wg)
    (key : KeypairId) (pkt : DataPacket)
    (run : (encryptPacket Env.checksumHelp key pkt).run w = .ok (result,v)) :
    HolderAccount temporary v.wg := by
  have same := (ProjectedAction.iff_run _ _ _).mp (encrypt_packet_store key pkt) w result v run
  apply account.store
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  simp only [holderStore,Origins.view,peersAt,packetKeyWords,device]

theorem TxInventory.encrypt_packet (inventory : TxInventory locals w.wg)
    (key : KeypairId) (pkt : DataPacket)
    (run : (encryptPacket Env.checksumHelp key pkt).run w = .ok (result,v)) :
    TxInventory locals v.wg := by
  have same := (ProjectedAction.iff_run _ _ _).mp (encrypt_packet_store key pkt) w result v run
  apply inventory.points
  have device : v.wg.dev = w.wg.dev := congrArg WGStoreView.dev same
  unfold ownershipPointView keyReferenceView
  simp only [keyAt,ownershipAt,peerAt,packetKeyWords,device]

theorem encrypt_tail_accounts (items : Option (List SkbId)) :
    Preserves (fun w : World => HolderAccount temporary w.wg ∧ TxInventory locals w.wg)
      (RxWorkers.encryptStepTailSource items) := by
  let Q := fun w : WGWorld => HolderAccount temporary w ∧ TxInventory locals w
  let P := fun w : World => Q w.wg
  have ambient {α : Type} (action : AmbientM α) : Preserves P (monadLift action : Leanux.M α) :=
    productAmbient_spec action P (fun _ _ hi => hi)
  have readNative (id : SkbId) : Preserves Q (getTxSkb id) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a p v b before run
    exact (Packets.getTxSkb_current id w v p a b run).1 ▸ before
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product Q _ (readNative id)
  have writeNative (id : SkbId) (bytes : List UInt8) :
      Preserves Q (setTxSkb id (fun p => {p with bytes})) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    have same := (ProjectedAction.iff_run_ambient _ _ _).mp
      (ownershipPoints_holderStore _ (setTx_holderStore id (fun p => {p with bytes}) (fun _ => rfl)))
      w a result v b run
    exact ⟨before.1.points same,before.2.points same⟩
  have write (id : SkbId) (bytes : List UInt8) :
      Preserves P (monadLift (setTxSkb id (fun p => {p with bytes})) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (writeNative id bytes)
  have publishNative (batch : List SkbId) (state : PacketState) :
      Preserves Q (enqueuePerPeerTx batch state) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact ⟨before.1.publish_tx batch state a b run,before.2.publish batch state a b run⟩
  have publish (batch : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx batch state) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (publishNative batch state)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    exact ⟨before.1.encrypt_packet key pkt run,before.2.encrypt_packet key pkt run⟩
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]

end Leanux.Proofs.WG.RetirementSecurity
