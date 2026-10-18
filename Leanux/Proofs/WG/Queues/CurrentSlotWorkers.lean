import Leanux.Proofs.WG.Queues.CurrentSlotStack
import Leanux.Proofs.WG.Origins.OwnerEncrypt

/-! Actual crypt-worker source cuts preserve three-slot compatibility. Product
softirq, IRQ and checksum callbacks retain their original arbitrary scope. -/
namespace Leanux.Proofs.WG.CurrentSlots
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues

theorem decryptPacket_preserves (pkt : RxPacket) : Preserves Inv (decryptPacket pkt) := by
  unfold decryptPacket WG.orM
  simp (config := {zeta := false}) only [branch,branchCmp,hiddenAlloc,invariant]
  repeat' slot_traffic_step

theorem prepareSource_preserves : Preserves Inv RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta := false}) only [branch,invariant,getRxSkb,setRxSkb]
  repeat' first
    | (rx_retention_head decryptPacket; exact decryptPacket_preserves _)
    | (rx_retention_head RxWorkers.publishSource; exact fields_preserves (project := id) (publish_fields _ _))
    | slot_packet_step
    | slot_traffic_step

theorem decryptStep_preserves (softirq irq : Leanux.M Unit)
    (hs : Preserves (fun w : World => Inv w.wg) softirq)
    (hi : Preserves (fun w : World => Inv w.wg) irq) :
    Preserves (fun w : World => Inv w.wg) (decryptStep softirq irq) := by
  rw [← RxWorkers.decrypt_source]
  unfold RxWorkers.decryptSource
  apply preserves_bind hs
  intro _
  apply preserves_bind (PublicationPoll.native_product Inv _ prepareSource_preserves)
  intro result
  cases result with
  | none => exact preserves_pure false
  | some pid =>
    exact preserves_bind hi fun _ =>
      preserves_bind (PublicationPoll.native_product Inv _ (peerPut_preserves (some pid))) fun _ =>
        preserves_bind hs (fun _ => preserves_pure true)

theorem encryptPacket_preserves (checksum : WG.Packet → Leanux.M WG.Packet)
    (hc : ∀ p, Preserves (fun w : World => Inv w.wg) (checksum p))
    (key : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World => Inv w.wg) (encryptPacket checksum key pkt) := by
  let P := fun w : World => Inv w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product Inv _ ((calculateSkbPadding_sameWGWorld _ _).wp Inv)
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) := by
    apply PublicationPoll.native_product Inv
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi hr
    exact (KeyTimes.getKeypair_return key w v k a b hr).1 ▸ hi
  routing_tx_source [encryptPacket] using [padding,hc,keySpec,ambient]

theorem encryptTail_preserves (item : Option (List SkbId)) :
    Preserves (fun w : World => Inv w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World => Inv w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) := by
    apply PublicationPoll.native_product Inv
    simp only [monadLift_self]
    repeat' slot_packet_step
  have write (id : SkbId) (f : DataPacket → DataPacket) :
      Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) := by
    apply PublicationPoll.native_product Inv
    simp only [monadLift_self]
    repeat' slot_packet_step
  have publish (xs : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product Inv _
      ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.enqueuePeer_preserves) xs state)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) :=
    encryptPacket_preserves Env.checksumHelp (fun p => (checksumHelp_sameWorld p).wp P) key pkt
  have stepSpec : Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]
  have needSpec : Preserves P (Env.condResched .encryptWorker) :=
    product_store_preserves (condResched_sameKernel _)
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [stepSpec,needSpec,ambient]

theorem encryptPoll_preserves : Preserves Inv TxRing.pollSource := by
  unfold TxRing.pollSource
  repeat' slot_traffic_step

end Leanux.Proofs.WG.CurrentSlots
