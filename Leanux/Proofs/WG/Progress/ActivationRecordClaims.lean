import Leanux.Proofs.WG.Progress.ActivationRecordSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env
/-- A projected composition rule for actual activation records. Concrete
iteration contracts remain hypotheses and must be discharged separately. -/
theorem original_activation_decrease_of_iterations (worker : Worker)
    (iteration : ∀ a : Activation, a.worker = worker → ∀ records,
      Campaign2.Product.Ensures (Activation.iter a)
        (fun s => s.ambient.hidden = some records)
        (fun result s => Tail records s.ambient.hidden ∧
          (result = .yielded → StrictTail records s.ambient.hidden)))
    (a : Activation) (same : a.worker = worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Activation.run a)
      (fun s => s.ambient.hidden = some records)
      (fun _ s => StrictTail records s.ambient.hidden) := by
  have native := activation_strict_of_iterations worker
    (fun active equal input => (Leanux.Proofs.Framing.hoare_iff_run _ _ _).mpr
      (iteration active equal input)) a same records
  exact (Leanux.Proofs.Framing.hoare_iff_run _ _ _).mp native
end Leanux.Proofs.WG.Progress.RecordSuffix
