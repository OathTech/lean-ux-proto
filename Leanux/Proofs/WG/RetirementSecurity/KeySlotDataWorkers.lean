import Leanux.Proofs.WG.RetirementSecurity.KeySlotNapi
import Leanux.Proofs.WG.RetirementSecurity.OccurrenceWorkers

/-! Actual data and handshake worker iterations transport live key slots.
The existing source factors retain native softirq and scheduler placement. -/
namespace Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open Queues.RxCredits

theorem product_store {action : Leanux.M α} (same : SameProductStore action) :
    Preserves (fun w : World=>InvExcept pending w.wg) action := kernel_predicate kernel_stable same

theorem encrypt_packet (key : KeypairId) (pkt : DataPacket) :
    Preserves (fun w : World=>InvExcept pending w.wg) (encryptPacket Env.checksumHelp key pkt) := by
  let P := fun w : World=>InvExcept pending w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  have padding : Preserves P
      (monadLift (calculateSkbPadding pkt.plaintext.bytes.length pkt.plaintext.mtu) : Leanux.M Nat) :=
    PublicationPoll.native_product _ _ ((calculateSkbPadding_sameWGWorld _ _).wp (InvExcept pending))
  have keySpec : Preserves P (monadLift (getKeypair key) : Leanux.M Keypair) :=
    PublicationPoll.native_product _ _ (get_key key)
  have check (p : WG.Packet) : Preserves P (Env.checksumHelp p) :=
    (checksumHelp_sameWorld p).wp P
  routing_tx_source [encryptPacket] using [padding,check,keySpec,ambient]

theorem encrypt_tail (item : Option (List SkbId)) :
    Preserves (fun w : World=>InvExcept pending w.wg) (RxWorkers.encryptTailSource item) := by
  let P := fun w : World=>InvExcept pending w.wg
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  have read (id : SkbId) : Preserves P (monadLift (getTxSkb id) : Leanux.M DataPacket) := by
    apply PublicationPoll.native_product (InvExcept pending)
    unfold getTxSkb
    exact skb _
  have write (id : SkbId) (f : DataPacket→DataPacket) :
      Preserves P (monadLift (setTxSkb id f) : Leanux.M Unit) := by
    apply PublicationPoll.native_product (InvExcept pending)
    unfold setTxSkb
    exact skb _
  have publish (items : List SkbId) (state : PacketState) :
      Preserves P (monadLift (enqueuePerPeerTx items state) : Leanux.M Unit) :=
    PublicationPoll.native_product _ _ (publish_tx items state)
  have packet := encrypt_packet (pending:=pending)
  have step : Preserves P (RxWorkers.encryptStepTailSource item) := by
    routing_tx_source [RxWorkers.encryptStepTailSource] using [read,write,packet,publish,ambient]
  have need : Preserves P (Env.condResched .encryptWorker) := product_store (condResched_sameKernel _)
  routing_tx_source [RxWorkers.encryptTailSource,workerIter] using [step,need,ambient]

theorem encrypt_poll : Preserves (InvExcept pending) TxRing.pollSource := by
  unfold TxRing.pollSource
  repeat' key_slot_rx_step

theorem encrypt_iteration : Preserves (fun w : World=>InvExcept pending w.wg)
    (encryptIter Env.checksumHelp Env.napiSoftirq (Env.condResched .encryptWorker)) := by
  rw [RxWorkers.encrypt_source]
  exact preserves_bind (PublicationPoll.native_product _ _ encrypt_poll) fun item=>
    preserves_bind (KeySlotNapi.softirq pending) fun _=>encrypt_tail item

theorem decrypt_publish (id : SkbId) (state : PacketState) :
    Preserves (InvExcept pending) (RxWorkers.publishSource id state) := by
  unfold RxWorkers.publishSource
  repeat' key_slot_rx_step

theorem decrypt_prepare : Preserves (InvExcept pending) RxWorkers.prepareSource := by
  unfold RxWorkers.prepareSource
  simp (config := {zeta:=false}) only [branch,invariant]
  repeat' first
    | (rx_retention_head decryptPacket; exact decrypt_packet _)
    | (rx_retention_head RxWorkers.publishSource; exact decrypt_publish _ _)
    | key_slot_rx_step

theorem decrypt_step : Preserves (fun w : World=>InvExcept pending w.wg)
    (decryptStep Env.napiSoftirq Env.napiIrqExit) := by
  rw [← RxWorkers.decrypt_source]
  unfold RxWorkers.decryptSource
  apply preserves_bind (KeySlotNapi.softirq pending)
  intro _
  apply preserves_bind (PublicationPoll.native_product _ _ decrypt_prepare)
  intro result
  cases result with
  | none=>exact preserves_pure false
  | some pid=>exact preserves_bind (KeySlotNapi.irqExit pending) fun _=>
      preserves_bind (PublicationPoll.native_product _ _ (peer_put (some pid))) fun _=>
        preserves_bind (KeySlotNapi.softirq pending) (fun _=>preserves_pure true)

theorem decrypt_iteration : Preserves (fun w : World=>InvExcept pending w.wg)
    (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) := by
  let P := fun w : World=>InvExcept pending w.wg
  have next : Preserves P (decryptStep Env.napiSoftirq Env.napiIrqExit) := decrypt_step
  have need : Preserves P (Env.condResched .decryptWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  routing_tx_source [decryptIter,workerIter] using [next,need,ambient]

theorem tx_iteration (pid : PeerId) : Preserves (fun w : World=>InvExcept pending w.wg)
    (txIter pid (Env.condResched .txWorker)) := by
  let P := fun w : World=>InvExcept pending w.wg
  have next : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product _ _ (tx_step pid)
  have need : Preserves P (Env.condResched .txWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  routing_tx_source [txIter,workerIter] using [next,need,ambient]

theorem handshake_iteration : Preserves (fun w : World=>InvExcept pending w.wg)
    (workerIter .receiveWorker none (liftWG receiveStep) (Env.condResched .receiveWorker)) := by
  let P := fun w : World=>InvExcept pending w.wg
  have next : Preserves P (liftWG receiveStep) := PublicationPoll.native_product _ _ receive_step
  have need : Preserves P (Env.condResched .receiveWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ hi=>hi)
  routing_tx_source [workerIter] using [next,need,ambient]

end Leanux.Proofs.WG.RetirementSecurity.KeySlotLiveness
