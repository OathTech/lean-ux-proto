import Leanux.Proofs.WG.Progress.ClearWorkerRecordSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal clear-worker record decrease. No executable-termination,
recordless-mode, or global scheduler adequacy conclusion is made here. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Proofs.Framing

/-- The original clear callback retains a suffix on every normal return,
including last-reference peer deletion. No residency or successful-leaf
premise is imposed. -/
theorem original_clear_callback_record_suffix (records : List HiddenRecord) (pid : PeerId) :
    Campaign2.Ensures (queuedExpiredZeroKeyMaterial pid)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro g a value after b pre run
  change a.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (clearCallback_retains records pid g)
    a (value,after) b (pre ▸ tail_self records) run

/-- Normal completion of the actual selected clear-work dispatch strictly
consumes supplied records. Selection, dequeue, sections, clearing, and the
final peer reference payment are all the original operations. This is a
normal-return decrease contract, not a total-evaluation or completion theorem. -/
theorem original_clear_worker_record_decrease (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.runOneClearWorker
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>StrictTail records s.ambient.hidden) := by
  intro before value after pre run
  change before.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (clearWorker_strict records)
    before value after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
