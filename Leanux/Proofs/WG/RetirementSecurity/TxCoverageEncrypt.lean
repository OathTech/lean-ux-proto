import Leanux.Proofs.WG.RetirementSecurity.TxCoverageDecrypt

/-! Native encryption updates existing TX cells and queue-alias marks; it
cannot lose a logical packet owner. NAPI during the iteration is composed
using the concrete original RX/stack contracts. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageEncrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open TxCoverageNative TxCoverageStack

theorem packet (key : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World=>TxCoverage locals w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact ready_store ((ProjectedAction.iff_run _ _ _).mp (encrypt_packet_store key pkt) w result v run) before

theorem step (items : Option (List SkbId)) :
    Preserves (fun w : World => TxCoverage locals w.wg)
      (RxWorkers.encryptStepTailSource items) := by
  let Q := fun w : WGWorld => TxCoverage locals w
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
    exact before.points same
  have write (id : SkbId) (bytes : List UInt8) :
      Preserves P (monadLift (setTxSkb id (fun p => {p with bytes})) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (writeNative id bytes)
  have publishNative (batch : List SkbId) (state : PacketState) :
      Preserves Q (enqueuePerPeerTx batch state) := by
    apply (hoare_iff_run_ambient _ _ _).mpr
    intro w a result v b before run
    cases result
    exact before.publish batch state a b run
  have publish (batch : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx batch state) : Leanux.M Unit) :=
    PublicationPoll.native_product Q _ (publishNative batch state)
  have packet (key : KeypairId) (pkt : DataPacket) :
      Preserves P (encryptPacket Env.checksumHelp key pkt) := by
    apply (hoare_iff_run _ _ _).mpr
    intro w result v before run
    exact (hoare_iff_run _ _ _).mp (packet key pkt) w result v before run
  change Preserves P _
  routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]

theorem poll : Preserves (TxCoverage locals) TxRing.pollSource := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.points ((ProjectedAction.iff_run_ambient _ _ _).mp
    OccurrenceEncrypt.poll_points w a result v b run)

theorem tail (item : Option (List SkbId)) :
    Preserves (fun w : World => TxCoverage locals w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World => TxCoverage locals w.wg
  have need : Preserves P (Env.condResched .encryptWorker) :=
    TxCoverageDecrypt.product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  have next : Preserves P (RxWorkers.encryptStepTailSource item) := step item
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [next,need,ambient]

theorem iteration : Preserves (fun w : World => TxCoverage locals w.wg)
    (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  rw [RxWorkers.encrypt_source]
  apply preserves_bind
    (PublicationPoll.native_product (TxCoverage locals) _ poll)
  intro item
  apply preserves_bind (TxCoverageNapi.softirq locals)
  intro _
  exact tail item

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageEncrypt
