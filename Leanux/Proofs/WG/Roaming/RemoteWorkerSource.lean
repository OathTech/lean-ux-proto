import Leanux.Proofs.WG.Roaming.RemoteWorkerFrames
import Leanux.Proofs.WG.Noise.TransmitRulesSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Roaming.RemoteWorkers
open Leanux Leanux.WG Noise Lifetimes Queues Leanux.Proofs.Framing Std.Do TimerDiscipline
open RemoteSilent

theorem txStep (entry : RemoteMap) (pid : PeerId) :
    Preserves (Retained entry) (WG.txStep pid) :=
  TransmitRules.step_preserves _ pid
    (fun f => (modifyPeer_remotes pid (fun p=>{p with txQueue:=f p.txQueue}) (fun _=>rfl)).wp (RemoteRetained entry))
    (fun item => (ensures_iff _ _ _).mp (dataCompletion entry pid item))
    (fun kid now => (keypairPut_frame kid now).wp (RemoteRetained entry))
    ((ensures_iff _ _ _).mp (peerPut_remotes (some pid) entry))
    (fun a => (packet_frame a).wp (RemoteRetained entry))
    (fun q => (RemoteCompletion.store_remotes (prevQueuePeek_sameWGStore q)).wp (RemoteRetained entry))

theorem txIter (entry : RemoteMap) (pid : PeerId) :
    Preserves (fun w : World=>Retained entry w.wg)
      (WG.txIter pid (Env.condResched .txWorker)) := by
  let P := fun w : World=>Retained entry w.wg
  have step : Preserves P (monadLift (WG.txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product (Retained entry) _ (txStep entry pid)
  have need : Preserves P (Env.condResched .txWorker) :=
    product_store entry _ (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  routing_tx_source [WG.txIter,workerIter] using [step,need,ambient]

theorem encryptPoll_frame : SameView destinationAt TxRing.pollSource := by
  unfold TxRing.pollSource
  exact (RemoteCompletion.store_remotes getDev_sameWGStore).bind (fun d =>
    (modifyDev_remotes (fun old=>{old with encryptQueue:=d.encryptQueue.consume.2}) (fun _=>rfl)).bind
      (fun _=>SameView.pure destinationAt d.encryptQueue.consume.1))

theorem enqueue (entry : RemoteMap) (item : List SkbId) (state : PacketState) :
    Preserves (Retained entry) (enqueuePerPeerTx item state) :=
  (ensures_iff _ _ _).mp (staging_remotes _
    (fun g=>(ensures_iff _ _ _).mpr (Index.StagingRich.enqueuePerPeerTx_rich item state g)) entry)

theorem encryptPacket (entry : RemoteMap) (key : KeypairId) (packet : DataPacket) :
    Preserves (fun w : World=>Retained entry w.wg)
      (WG.encryptPacket Env.checksumHelp key packet) := by
  let P := fun w : World=>Retained entry w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  exact Index.EncryptCore.packet_preserves_source P key packet
    (PublicationPoll.native_product (Retained entry) _
      ((calculateSkbPadding_sameWGWorld _ _).wp (Retained entry)))
    (fun p => (checksumHelp_sameWorld p).wp P)
    (PublicationPoll.native_product (Retained entry) _ ((getKeypair_frame key).wp (RemoteRetained entry)))
    ambient

theorem encryptTail (entry : RemoteMap) (item : Option (List SkbId)) :
    Preserves (fun w : World=>Retained entry w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World=>Retained entry w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  exact Index.EncryptCore.tail_preserves_source P item
    (fun id => PublicationPoll.native_product (Retained entry) _
      ((packet_frame (SkbStore.getTx id)).wp (RemoteRetained entry)))
    (fun id f => PublicationPoll.native_product (Retained entry) _
      ((packet_frame (SkbStore.setTx id f)).wp (RemoteRetained entry)))
    (fun xs state => PublicationPoll.native_product (Retained entry) _ (enqueue entry xs state))
    (encryptPacket entry) (product_store entry _ (condResched_sameKernel _)) ambient

end Leanux.Proofs.WG.Roaming.RemoteWorkers
