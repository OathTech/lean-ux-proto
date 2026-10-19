import Leanux.Proofs.WG.TransmitSecurity.EncryptionHistoryFrames

/-! Native non-encryption worker frames join historical exclusion with
physical packet ownership; they make no assumption about journal reachability. -/
namespace Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open RetirementSecurity

theorem receive_native : Preserves (fun w : World => Native past active w.wg)
    (workerIter .receiveWorker none (liftWG receiveStep) (Env.condResched .receiveWorker)) := by
  apply product_join ?_ OccurrenceHandshake.iteration
  let P := fun w : World => EncryptionPast.Ready past active w.wg
  have step : Preserves P (liftWG receiveStep) :=
    PublicationPoll.native_product _ _ EncryptionPast.Handshake.receive_step
  have need : Preserves P (Env.condResched .receiveWorker) :=
    EncryptionPast.product_store (condResched_sameKernel _)
  routing_tx_source [workerIter] using [step,need]

theorem work_native (f : List PeerId → List PeerId) :
    Preserves (Native past active) (modifyDev fun d => {d with txWorkQueue := f d.txWorkQueue}) := by
  apply native_join ?_ (OccurrenceScheduler.work_queue f)
  apply EncryptionPast.ready_frame
  · exact TxDisposition.LiveFrontier.ready_frame
      (metadata_modifyDev _ (fun _ => rfl))
      (by apply (ProjectedAction.iff_run_ambient _ _ _).mpr
          intro w a x v b run
          cases run
          simp only [TxRing.nativeCell,Option.map_map,Function.comp_def])
  · exact EncryptionPast.modify _ (fun _ => rfl) (fun _ => rfl)

end Leanux.Proofs.WG.TransmitSecurity.EncryptionHistory
