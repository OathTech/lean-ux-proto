import Leanux.Proofs.WG.HandshakeSecurity.ResponderDecryptHistory

namespace Leanux.Proofs.WG.HandshakeSecurity.Responder
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Std.Do
open Lifetimes Queues RxCredits

theorem publication_native (xs : List SkbId) (state : PacketState) (confirmed : List Nat) :
    Preserves (History.Native confirmed) (enqueuePerPeerTx xs state) := by
  apply native_retained _ (publication_keyEffect (allowed := NoPromotion) xs state)
    ((pinned_const _private.Leanux.Proofs.WG.Queues.CurrentSlotTraffic.«0».Leanux.Proofs.WG.CurrentSlots.enqueuePeer_preserves) xs state) confirmed
  apply (ProjectedAction.iff_run_ambient _ _ _).mpr
  intro w a result v b run
  rw [(ProjectedAction.iff_run_ambient _ _ _).mp (publication_core xs state) w a result v b run]
  exact Retains.refl _

theorem encrypt_native (key : KeypairId) (pkt : DataPacket) (confirmed : List Nat) :
    Preserves (fun w : World => History.Native confirmed w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  let P := fun w : World => History.Native confirmed w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (History.Native confirmed))
  have checksumSpec (p : WG.Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) := by
    apply PublicationPoll.native_product
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a k v b hi hr
    exact (KeyTimes.getKeypair_return key w v k a b hr).1 ▸ hi
  routing_tx_source [encryptPacket] using [padding,checksumSpec,keySpec,ambient]

theorem encryptTail_native (item : Option (List SkbId)) (confirmed : List Nat) :
    Preserves (fun w : World => History.Native confirmed w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World => History.Native confirmed w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi => hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) := by
    apply PublicationPoll.native_product
    unfold getTxSkb
    exact native_skb _ confirmed
  have write (id : SkbId) (f : DataPacket → DataPacket) :
      Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) := by
    apply PublicationPoll.native_product
    unfold setTxSkb
    exact native_skb _ confirmed
  have publish (xs : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx xs state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (publication_native xs state confirmed)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := encrypt_native key pkt confirmed
  have stepSpec : Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]
  have needSpec : Preserves P (Env.condResched .encryptWorker) :=
    native_product_store (condResched_sameKernel _) confirmed
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [stepSpec,needSpec,ambient]

theorem encryptPoll_native (confirmed : List Nat) :
    Preserves (History.Native confirmed) TxRing.pollSource := by
  unfold TxRing.pollSource
  apply preserves_bind (native_store getDev_sameWGStore confirmed)
  intro d
  apply preserves_bind (modify_native
    (fun dev => {dev with encryptQueue := d.encryptQueue.consume.2})
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) confirmed)
  intro _
  exact preserves_pure _

end Leanux.Proofs.WG.HandshakeSecurity.Responder
