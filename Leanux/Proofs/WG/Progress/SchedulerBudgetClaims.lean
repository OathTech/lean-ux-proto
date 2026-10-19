import Leanux.Proofs.WG.Progress.SchedulerBudgetSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected adequacy of the original scheduler's record-derived outer budget. Neither theorem asserts that callbacks return normally or that pending work is empty. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env

/-- With the actual record-derived number of turns, every normal loop result carries the source completion marker. -/
theorem scheduler_loop_budget_adequate (stack : Option Worker) (records : List HiddenRecord) :
    Campaign2.Product.Ensures
      (forIn (List.range' 0 (records.length+1)) ((none,()) : Option Unit × Unit)
        (fun _ _=>scheduleTurn stack))
      (fun s=>s.ambient.hidden=some records) (fun result _=>result=(some (),())) := by
  intro before result after present run
  exact scheduleLoop_normal_done stack _ records before after result present
    (by simp only [List.length_range']; omega) run

/-- All outcomes of the original schedule agree with its same captured-budget loop followed by unit return. This removes only its own impossible exhaustion arm, retaining every callback error. -/
theorem scheduler_record_budget_source (stack : Option Worker) (records : List HiddenRecord) :
    Campaign2.Product.AgreesOn (fun s=>s.ambient.hidden=some records)
      (Env.schedule stack)
      (do
        let _ ← forIn (List.range' 0 (records.length+1)) ((none,()) : Option Unit × Unit)
          (fun _ _=>scheduleTurn stack)
        pure ()) := by
  intro before present
  exact congrArg Campaign2.Product.observeResult (schedule_supplied_source stack records before present)

end Leanux.Proofs.WG.Progress.RecordSuffix
