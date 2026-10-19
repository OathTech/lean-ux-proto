import Leanux.Proofs.WG.RetirementSecurity.TxCoverageEncrypt

/-! TX disposal and the receive worker retain coverage of every resident TX cell.
The final TX release removes the cell together with its queue ownership. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCoverageWorkers
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do

theorem step (pid : PeerId) : Preserves (TxCoverage locals) (txStep pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact before.step pid a b run

theorem transmit (pid : PeerId) : Preserves (fun w : World => TxCoverage locals w.wg)
    (txIter pid (Env.condResched .txWorker)) := by
  let P := fun w : World => TxCoverage locals w.wg
  have next : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product (TxCoverage locals) _ (step pid)
  have need : Preserves P (Env.condResched .txWorker) :=
    TxCoverageDecrypt.product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [txIter,workerIter] using [next,need,ambient]

theorem receive : Preserves (fun w : World => TxCoverage locals w.wg)
    (workerIter .receiveWorker none (liftWG receiveStep) (Env.condResched .receiveWorker)) := by
  let P := fun w : World => TxCoverage locals w.wg
  have next : Preserves P (liftWG receiveStep) :=
    PublicationPoll.native_product (TxCoverage locals) _ TxCoverageNative.receive_step
  have need : Preserves P (Env.condResched .receiveWorker) :=
    TxCoverageDecrypt.product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [workerIter] using [next,need,ambient]

end Leanux.Proofs.WG.RetirementSecurity.TxCoverageWorkers
