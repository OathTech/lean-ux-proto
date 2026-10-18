import Leanux.Proofs.WG.RetirementSecurity.OccurrenceEncrypt

/-! Native TX disposal uses the already derived physical separation and
readiness phase. It preserves the occurrence invariant without an independent
peer-credit premise; key-holder safety remains a distinct claim. -/
namespace Leanux.Proofs.WG.RetirementSecurity.OccurrenceTx
open Leanux Leanux.WG Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Queues Std.Do
open OccurrenceStack

theorem step (pid : PeerId) : Preserves (Ready locals active) (txStep pid) := by
  apply (hoare_iff_run_ambient _ _ _).mpr
  intro w a result v b before run
  exact ⟨Allocated.native (txStepPrefix_erases pid)
      (txStepPrefix_preserves_ambient allocationAmbient allocationTx allocationSocket pid) before.1 a b run,
    before.2.1.step pid a b run,before.2.2.step before.2.1 pid a b run⟩

theorem iteration (pid : PeerId) : Preserves (fun w : World => Ready locals active w.wg)
    (txIter pid (Env.condResched .txWorker)) := by
  let P := fun w : World => Ready locals active w.wg
  have next : Preserves P (monadLift (txStep pid) : Leanux.M Bool) :=
    PublicationPoll.native_product (Ready locals active) _ (step pid)
  have need : Preserves P (Env.condResched .txWorker) :=
    OccurrenceDecrypt.product_store (condResched_sameKernel _)
  have ambient {α : Type} (a : AmbientM α) : Preserves P (monadLift a : Leanux.M α) :=
    productAmbient_spec a P (fun _ _ before => before)
  routing_tx_source [txIter,workerIter] using [next,need,ambient]

end Leanux.Proofs.WG.RetirementSecurity.OccurrenceTx
