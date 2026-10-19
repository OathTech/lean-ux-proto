import Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertextNativeNapi

/-! Native decryption changes receive material and can enter NAPI; both
paths preserve the TX ready-ciphertext projection. -/
namespace Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Decrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open RetirementSecurity Native Stack

theorem prepare_inv : Preserves Inv RxWorkers.prepareSource := by
  have packet (pkt : RxPacket) := Native.wire (OccurrenceDecrypt.packet_queues pkt) (OccurrenceDecrypt.packet_wire pkt)
  have publish (id : SkbId) (state : PacketState) := Native.wire (OccurrenceDecrypt.publish_queues id state) (OccurrenceDecrypt.publish_wire id state)
  have read (id : SkbId) := ReceiveOccurrences.get_rx id Inv
  have write (id : SkbId) (f : RxPacket → RxPacket) := Receive.passive
    (ReceiveOccurrences.set_rx_wire id f) (ReceiveOccurrences.skb_queues _)
  have device := Receive.store  getDev_sameWGStore
  have ring (queue : PtrRing SkbId) : Preserves Inv
      (modifyDev fun d => {d with decryptQueue := queue}) :=
    Receive.modify _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves Inv (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [RxWorkers.prepareSource,branch,invariant] using [packet,publish,read,write,device,ring,ambient]

theorem prepare : Preserves (Coherent locals active) RxWorkers.prepareSource :=
  coherent_join OccurrenceDecrypt.prepare prepare_inv

theorem product_store {action : Leanux.M α} (frame : SameProductStore action) :
    Preserves (fun w : World => Coherent locals active w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact ready_store (congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w result v run)) before

theorem step : Preserves (fun w : World => Coherent locals active w.wg)
    (decryptStep Env.napiSoftirq Env.napiIrqExit) := by
  rw [← RxWorkers.decrypt_source]
  unfold RxWorkers.decryptSource
  apply preserves_bind (Napi.softirq locals active)
  intro _
  apply preserves_bind (PublicationPoll.native_product (Coherent locals active) _ prepare)
  intro result
  cases result with
  | none => exact preserves_pure false
  | some pid => exact preserves_bind (Napi.irqExit locals active) fun _ =>
      preserves_bind (PublicationPoll.native_product (Coherent locals active) _ (Poll.peer_put (some pid))) fun _ =>
        preserves_bind (Napi.softirq locals active) (fun _ => preserves_pure true)

theorem iteration : Preserves (fun w : World => Coherent locals active w.wg)
    (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) := by
  let P := fun w : World => Coherent locals active w.wg
  have next : Preserves P (decryptStep Env.napiSoftirq Env.napiIrqExit) := step
  have need : Preserves P (Env.condResched .decryptWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [decryptIter,workerIter] using [next,need,ambient]

end Leanux.Proofs.WG.RetirementSecurity.ReadyCiphertext.Decrypt
