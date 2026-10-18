import Leanux.Proofs.WG.RetirementSecurity.OccurrenceDecryptFrames

/-! Original decrypt worker transport includes both native NAPI placements,
publication, its retained peer loan, and the final scheduler checkpoint. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceDecrypt
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open OccurrenceStack

theorem product_store {action : Leanux.M α} (frame : SameProductStore action) :
    Preserves (fun w : World => Ready locals active w.wg) action := by
  apply (hoare_iff_run _ _ _).mpr
  intro w result v before run
  exact ready_store (congrArg (fun s : ProductStore43 => s.2.2.2)
    ((ProjectedAction.iff_run _ _ _).mp frame w result v run)) before

theorem step : Preserves (fun w : World => Ready locals active w.wg)
    (decryptStep Env.napiSoftirq Env.napiIrqExit) := by
  rw [← RxWorkers.decrypt_source]
  unfold RxWorkers.decryptSource
  apply preserves_bind (OccurrenceNapi.softirq locals active)
  intro _
  apply preserves_bind (PublicationPoll.native_product (Ready locals active) _ prepare)
  intro result
  cases result with
  | none => exact preserves_pure false
  | some pid => exact preserves_bind (OccurrenceNapi.irqExit locals active) fun _ =>
      preserves_bind (PublicationPoll.native_product (Ready locals active) _ (RxPollOccurrences.peer_put (some pid))) fun _ =>
        preserves_bind (OccurrenceNapi.softirq locals active) (fun _ => preserves_pure true)

theorem iteration : Preserves (fun w : World => Ready locals active w.wg)
    (decryptIter Env.napiSoftirq Env.napiIrqExit (Env.condResched .decryptWorker)) := by
  let P := fun w : World => Ready locals active w.wg
  have next : Preserves P (decryptStep Env.napiSoftirq Env.napiIrqExit) := step
  have need : Preserves P (Env.condResched .decryptWorker) := product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [decryptIter,workerIter] using [next,need,ambient]

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceDecrypt
