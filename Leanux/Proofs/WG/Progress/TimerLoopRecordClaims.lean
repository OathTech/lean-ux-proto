import Leanux.Proofs.WG.Progress.TimerLoopRecordSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Whole actual timer-loop suffix preservation. Normal return does not
assert that a timer fired or that every queued unit was completed. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.Proofs.Framing

theorem runTimers_record_suffix (records : List HiddenRecord) (bound : UInt64) :
    Campaign2.Product.Ensures (Env.runTimers bound)
      (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro before value after pre run
  change before.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (runTimers_retains records bound)
    before value after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
