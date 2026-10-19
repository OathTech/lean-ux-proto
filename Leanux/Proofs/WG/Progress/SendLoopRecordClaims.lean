import Leanux.Proofs.WG.Progress.SendLoopRecordSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected original send-loop record effects and adequate captured fuel. All callback Stops are retained. No callback termination, normal-return existence, recordless-mode adequacy or global pending-work emptiness is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

theorem sendCompletionTurn_record_suffix (records : List HiddenRecord)
    (index : Nat) (state : Option Unit×Unit) :
    Campaign2.Product.Ensures (sendCompletionTurn index state)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>Tail records s.ambient.hidden ∧
        (∀ value,result=.yield value→StrictTail records s.ambient.hidden)) := by
  intro before value after present run
  change before.ambient.hidden=some records at present
  exact (hoare_iff_run _ _ _).mp (sendCompletionTurn_record_effect records index state)
    before value after (present ▸ tail_self records) run

theorem sendWorkers_loop_budget_adequate (records : List HiddenRecord) :
    Campaign2.Product.Ensures
      (forIn (List.range' 0 (records.length+1)) ((none,()) : Option Unit×Unit) sendCompletionTurn)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>result.1.isSome=true ∧ ∃ d,s.wg.device=some d ∧ d.sendWorkQueue=[]) := by
  intro before value after present run
  change before.ambient.hidden=some records at present
  have complete:=sendCompletionLoop_normal_done (List.range' 0 (records.length+1))
    records before after value present (by simp only [List.length_range']; omega) run
  exact ⟨complete,sendCompletionLoop_done _ _ _ _ run complete⟩

theorem runSendWorkers_record_suffix (records : List HiddenRecord) :
    Campaign2.Product.Ensures Env.runSendWorkers
      (fun s=>s.ambient.hidden=some records) (fun _ s=>Tail records s.ambient.hidden) := by
  intro before value after present run
  change before.ambient.hidden=some records at present
  exact (hoare_iff_run _ _ _).mp (runSendWorkers_retains records)
    before value after (present ▸ tail_self records) run

theorem sendWorkers_record_budget_source (records : List HiddenRecord) :
    Campaign2.Product.AgreesOn (fun s=>s.ambient.hidden=some records)
      Env.runSendWorkers
      (do
        if (←getWG).dev.isNone then return
        requireNoCryptWork
        modifyWG fun g=>{g with queuedThisCall:=[]}
        let _←forIn (List.range' 0 (records.length+1))
          ((none,()) : Option Unit×Unit) sendCompletionTurn
        pure ()) := by
  intro before present
  exact congrArg Campaign2.Product.observeResult (runSendWorkers_supplied_source records before present)

end Leanux.Proofs.WG.Progress.RecordSuffix
