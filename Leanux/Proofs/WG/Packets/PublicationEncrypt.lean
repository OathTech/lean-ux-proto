import Leanux.Proofs.WG.Packets.PublicationWorkers
import Leanux.Proofs.WG.Origins.OwnerEncrypt

/-! Encryption retains receive certificates through its actual TX writes.
The packet adapter requires an RX frame; arbitrary SkbM writes are not framed. -/
namespace Leanux.Proofs.WG.PublicationJoint
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Std.Do
open Lifetimes Queues Queues.RxCredits

theorem mixed (g : PrefixM LifetimeEvent α) (a : Leanux.M α)
    (owner : OwnerChecks.Preserves (RxHistory.mixed g)) (erases : ErasesPrefix g a)
    (preserves : ∀ history, Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) a) :
    Preserves (RxHistory.mixed g) :=
  quiet _ a owner (Appends.focus _ _ _)
    (RxHistory.mixed_erases erases)
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerConfiguration.«0».Leanux.Proofs.WG.OwnerConfiguration.mixed_frame)
      PublicationChecks.sensitive (fun _ => rfl) _) preserves

private theorem skb {α : Type} (a : SkbM α)
    (rx : SameView RxDisposition.nativeRxStore (liftSkb a)) (history : List RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) (liftSkb a) := by
  apply PublicationFrontier.preserves_of_configured _ rx
  intro initial
  apply hoare_liftSkb
  intro w d packets hi hd
  simpa only [ConfiguredIdentity.view,ConfiguredIdentity.state,hd,Option.map_some] using hi

private theorem product_store (a : Leanux.M α) (frame : SameProductStore a)
    (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg) a :=
  (pinned_const _private.Leanux.Proofs.WG.Packets.PublicationFrontierPoll.«0».Leanux.Proofs.WG.PublicationFrontier.product_store)
    a frame history

private theorem encrypt (key : KeypairId) (pkt : DataPacket) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (encryptPacket Env.checksumHelp key pkt) := by
  let P := fun w : World => PublicationFrontier.Inv history w.wg
  have ambient {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Framing.Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (PublicationFrontier.Inv history))
  have checksumSpec (p : WG.Packet) : Framing.Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have keySpec : Framing.Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) := by
    apply PublicationPoll.native_product
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi hr
    exact (KeyTimes.getKeypair_return key w v k a b hr).1 ▸ hi
  routing_tx_source [encryptPacket] using [padding,checksumSpec,keySpec,ambient]

private theorem enqueue (xs : List SkbId) (state : PacketState) (history : List RxHistory.Event) :
    Framing.Preserves (PublicationFrontier.Inv history) (enqueuePerPeerTx xs state) :=
  PublicationFrontier.preserves_of_geometry _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerCompletion.«0».Leanux.Proofs.WG.OwnerCompletion.enqueuePeer_geometry) xs state)
    ((pinned_const _private.Leanux.Proofs.WG.Packets.PublicationCompletion.«0».Leanux.Proofs.WG.PublicationCompletion.enqueue_peers) xs state)
    history

theorem encryptTail_frontier (item : Option (List SkbId)) (history : List RxHistory.Event) :
    Framing.Preserves (fun w : World => PublicationFrontier.Inv history w.wg)
      (RxWorkers.encryptTailSource item) := by
  let P := fun w : World => PublicationFrontier.Inv history w.wg
  have ambient {α : Type} (a : AmbientM α) : Framing.Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Framing.Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) :=
    PublicationPoll.native_product _ _
      (skb _ ((getTx_protect id).of_factor (fun v => v.2.1) _ (fun _ => rfl)) history)
  have write (id : SkbId) (f : DataPacket → DataPacket) :
      Framing.Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _
      (skb _ ((setTx_protect id f).of_factor (fun v => v.2.1) _ (fun _ => rfl)) history)
  have publish (xs : List SkbId) (state : PacketState) :
      Framing.Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (enqueue xs state history)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Framing.Preserves P (encryptPacket Env.checksumHelp key pkt) := encrypt key pkt history
  have stepSpec : Framing.Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]
  have needSpec : Framing.Preserves P (Env.condResched .encryptWorker) :=
    product_store _ (condResched_sameKernel _) history
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [stepSpec,needSpec,ambient]

private theorem encryptPoll :
    Preserves (RxHistory.mixed (liftWGObserver (liftWGPrefix TxRing.pollSource))) := by
  apply native_mixed _ TxRing.pollSource
    (pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEncrypt.«0».Leanux.Proofs.WG.OwnerEncrypt.poll)
    (erasesStatePrefix_lift _)
  intro history
  unfold TxRing.pollSource
  apply preserves_bind (PublicationFrontier.store_preserves getDev_sameWGStore history)
  intro d
  apply preserves_bind (PublicationFrontier.modifyDev_preserves
    (fun dev => {dev with encryptQueue := d.encryptQueue.consume.2})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl) history)
  intro _
  exact preserves_pure _

private theorem encryptTail (item : Option (List SkbId)) :
    Preserves (RxHistory.mixed (RxWorkers.encryptTail item)) :=
  mixed _ _
    ((pinned_const _private.Leanux.Proofs.WG.Origins.OwnerEncrypt.«0».Leanux.Proofs.WG.OwnerEncrypt.tail) item)
    (RxWorkers.encryptTail_erases item) (encryptTail_frontier item)

theorem encryptIteration : Preserves RxHistory.encryptIteration := by
  unfold RxHistory.encryptIteration
  exact encryptPoll.bind (fun item => napiSoftirq.bind (fun _ => encryptTail item))

end Leanux.Proofs.WG.PublicationJoint
