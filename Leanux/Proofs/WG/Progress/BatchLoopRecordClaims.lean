import Leanux.Proofs.WG.Progress.BatchLoopRecordSource

/-! Projected record suffix of the recorded batch loop before its completion guard. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Env Leanux.Proofs.Framing

theorem afterBatchRecordedLoop_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures afterBatchRecordedLoop
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro before value after pre run
  change before.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (afterBatchRecordedLoop_retains records)
    before value after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
