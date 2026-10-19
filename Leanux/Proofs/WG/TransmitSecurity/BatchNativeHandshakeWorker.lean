import Leanux.Proofs.WG.TransmitSecurity.BatchNativeControls

/-! Native handshake worker iterations preserve batch alignment across the
actual receiver and scheduler checkpoint. -/
namespace Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open RetirementSecurity

theorem iteration : Preserves (fun w : World => Coherent locals active w.wg)
    (workerIter .receiveWorker none (liftWG receiveStep) (Env.condResched .receiveWorker)) := by
  let P := fun w : World => Coherent locals active w.wg
  have next : Preserves P (liftWG receiveStep) :=
    PublicationPoll.native_product (Coherent locals active) _ receive_step
  have need : Preserves P (Env.condResched .receiveWorker) :=
    Decrypt.product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [workerIter] using [next,need,ambient]

end Leanux.Proofs.WG.TransmitSecurity.BatchCoherence.Native
