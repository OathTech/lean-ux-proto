import Leanux.Proofs.WG.Progress.TimerBudgetSource
import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeClaims

/-! Projected timer budget adequacy with exact original episode linkage. Errors are preserved and unconstrained; normal completion yields an actual done receipt, or the separately represented absent-device branch. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env
open Leanux.Proofs.WG.TimerDiscipline

/-- The source-derived number of turns cannot be consumed entirely by yielded turns on a normal observed run. -/
theorem timerOuterTurns_record_budget (jPass : UInt64) (records : List HiddenRecord)
    (control : TimerOuterControl) :
    Campaign2.Product.Ensures
      (observedTimerOuterTurns jPass (List.range' 0 (records.length+1)) control)
      (fun s=>s.ambient.hidden=some records)
      (fun result _=>∃ front last,result.2=front++[last] ∧ last.result=.done result.1) := by
  intro before result after present run
  exact timerOuterTurns_budget_done jPass _ control records before after result.1 result.2 present
    (by simp only [List.length_range']; omega) run

/-- Normal whole episodes separate absent-device handling from an actual done turn. -/
theorem runTimersEpisode_record_budget (jPass : UInt64) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (observedRunTimersEpisode jPass)
      (fun s=>s.ambient.hidden=some records)
      (fun result _=>TimerEpisodeBudgetDone records result.1) := by
  intro before result after present run
  exact runTimersEpisode_budget_done jPass records before after result.1 result.2 present run

/-- The original operation's exact outcome is inspected. On normal return its own existing observed episode has the valid source chain and budget-exit fact; Stop outcomes are neither changed nor claimed to retain this non-prefix observer's receipts. -/
theorem runTimers_record_budget (jPass : UInt64) (records : List HiddenRecord) :
    Campaign2.Product.Observes (Env.runTimers jPass)
      (fun s=>s.ambient.hidden=some records)
      (fun entry outcome=>match outcome with
        | .error _=>True
        | .ok (result,final)=>∃ receipt,
            OuterTimerEpisodeValid jPass entry receipt result final ∧
            TimerEpisodeBudgetDone records receipt) := by
  intro initial present
  have erase:=congrArg (fun action : Leanux.M Bool=>action.run initial)
    (observedRunTimersEpisode_erase jPass)
  change ((observedRunTimersEpisode jPass).run initial >>=
    fun out=>Except.ok (out.1.2,out.2))=(Env.runTimers jPass).run initial at erase
  cases observedRun : (observedRunTimersEpisode jPass).run initial with
  | error stop=>
    rw [observedRun] at erase
    rw [←erase]
    trivial
  | ok pair=>
    obtain ⟨⟨receipt,result⟩,final⟩:=pair
    rw [observedRun] at erase
    rw [←erase]
    exact ⟨receipt,runTimers_episode_receipt jPass (Campaign2.Product.snapshot initial)
      initial (receipt,result) final rfl observedRun,
      runTimersEpisode_budget_done jPass records initial final receipt result present observedRun⟩

end Leanux.Proofs.WG.Progress.RecordSuffix
