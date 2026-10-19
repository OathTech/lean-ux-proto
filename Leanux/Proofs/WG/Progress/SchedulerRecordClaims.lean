import Leanux.Proofs.WG.Progress.SchedulerRecordSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal-result suffixes for the original dispatcher, scheduler turn and whole scheduler. True dispatch and continuing turns consume records; Stops, fuel adequacy and global worker completion remain distinct. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.Logged

theorem dispatch_record_suffix (worker : Worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Env.dispatch worker) (fun s=>s.ambient.hidden=some records)
      (fun result s=>Tail records s.ambient.hidden ∧
        (result=true→StrictTail records s.ambient.hidden)) := by
  intro before result after pre run
  change before.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (dispatch_record_effect worker records)
    before result after (pre ▸ tail_self records) run

theorem scheduleTurn_record_suffix (stack : Option Worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (scheduleTurn stack) (fun s=>s.ambient.hidden=some records)
      (fun result s=>Tail records s.ambient.hidden ∧
        (result=turnContinue→StrictTail records s.ambient.hidden)) := by
  intro before result after pre run
  change before.ambient.hidden=some records at pre
  refine ⟨(hoare_iff_run _ _ _).mp (scheduleTurn_retains records stack)
    before result after (pre ▸ tail_self records) run,?_⟩
  intro continued
  subst result
  exact scheduleTurn_continue_strict stack records before after pre run

theorem schedule_record_suffix (stack : Option Worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (Env.schedule stack) (fun s=>s.ambient.hidden=some records)
      (fun _ s=>Tail records s.ambient.hidden) := by
  intro before result after pre run
  change before.ambient.hidden=some records at pre
  exact (hoare_iff_run _ _ _).mp (schedule_retains records stack)
    before result after (pre ▸ tail_self records) run

end Leanux.Proofs.WG.Progress.RecordSuffix
