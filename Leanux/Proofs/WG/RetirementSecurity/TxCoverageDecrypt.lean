import Leanux.Proofs.WG.RetirementSecurity.TxCoverageNapi

/-! Actual decrypt preparation and NAPI placements preserve allocated TX
coverage. All source callbacks use their concrete native contracts. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageDecrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open TxCoverageNative TxCoverageStack

theorem prepare : Preserves (TxCoverage locals) RxWorkers.prepareSource := by
  have packet (pkt : RxPacket) := TxCoverageNative.wire (locals:=locals) (OccurrenceDecrypt.packet_queues pkt) (OccurrenceDecrypt.packet_wire pkt)
  have publish (id : SkbId) (state : PacketState) := TxCoverageNative.wire (locals:=locals) (OccurrenceDecrypt.publish_queues id state) (OccurrenceDecrypt.publish_wire id state)
  have read (id : SkbId) := ReceiveOccurrences.get_rx id (TxCoverage locals)
  have write (id : SkbId) (f : RxPacket → RxPacket) := TxCoverageReceive.passive (locals:=locals)
    (ReceiveOccurrences.set_rx_wire id f) (ReceiveOccurrences.skb_queues _)
  have device := TxCoverageReceive.store (locals:=locals)  getDev_sameWGStore
  have ring (queue : PtrRing SkbId) : Preserves (TxCoverage locals)
      (modifyDev fun d => {d with decryptQueue := queue}) :=
    TxCoverageNative.modify_device _ (fun _ => rfl) (fun _ => rfl)
  have ambient {α : Type} (a : AmbientM α) : Preserves (TxCoverage locals) (monadLift a : WG.M α) :=
    hoare_liftAmbient a _
  rxstack_preserves_source [RxWorkers.prepareSource,branch,invariant] using [packet,publish,read,write,device,ring,ambient]

theorem product_store {action : Leanux.M α} (frame : SameProductStore action) :
    Preserves (fun w : World => TxCoverage locals w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact ready_store (congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w result v run)) before

theorem step : Preserves (fun w : World => TxCoverage locals w.wg)
    (decryptStep Env.napiSoftirq Env.napiIrqExit) := by
  rw [← RxWorkers.decrypt_source]
  unfold RxWorkers.decryptSource
  apply preserves_bind (TxCoverageNapi.softirq locals)
  intro _
  apply preserves_bind (PublicationPoll.native_product (TxCoverage locals) _ prepare)
  intro result
  cases result with
  | none => exact preserves_pure false
  | some pid => exact preserves_bind (TxCoverageNapi.irqExit locals) fun _ =>
      preserves_bind (PublicationPoll.native_product (TxCoverage locals) _ (TxCoverageNative.peer_put (some pid))) fun _ =>
        preserves_bind (TxCoverageNapi.softirq locals) (fun _ => preserves_pure true)

theorem iteration : Preserves (fun w : World => TxCoverage locals w.wg)
    (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) := by
  let P := fun w : World => TxCoverage locals w.wg
  have next : Preserves P (decryptStep Env.napiSoftirq Env.napiIrqExit) := step
  have need : Preserves P (Env.condResched .decryptWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [decryptIter,workerIter] using [next,need,ambient]

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageDecrypt
