import Leanux.Proofs.WG.Progress.BatchBudgetSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Supplied-record measures and exact budget adequacy of the original batch loop before its drain suffix. No callback success, finite evaluation, service or completion-guard conclusion is asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing

/-- Normal original turn effects, with strictness whenever that turn yields. -/
theorem batchTurn_record_effect (iteration : Nat) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (afterBatchRecordedTurn iteration ())
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>Tail records s.ambient.hidden ∧
        (result=.yield ()→StrictTail records s.ambient.hidden)) := by
  intro before result after present run
  change before.ambient.hidden=some records at present
  exact (hoare_iff_run _ _ _).mp (afterBatchRecordedTurn_record_effect records iteration)
    before result after (present ▸ tail_self records) run

/-- Any additional fuel leaves the original loop's exact outcome and projected final state unchanged. The original records.length+1 bound is captured at entry; the subsequent drain suffix is not part of either action. -/
theorem batch_loop_budget_adequate (records : List HiddenRecord) (extra : Nat) :
    Campaign2.Product.AgreesOn (fun s=>s.ambient.hidden=some records)
      afterBatchRecordedLoop
      (do
        let _ ← forIn (List.range' 0 (records.length+1+extra)) () afterBatchRecordedTurn
        pure ()) := by
  intro before present
  have equal:=afterBatchRecordedLoop_extra_turns records
    (List.range' (records.length+1) extra) before present
  have ranges : List.range' 0 (records.length+1)++List.range' (records.length+1) extra=
      List.range' 0 (records.length+1+extra) := by
    simpa only [Nat.one_mul,Nat.zero_add] using
      (List.range'_append (s:=0) (m:=records.length+1) (n:=extra) (step:=1))
  rw [ranges] at equal
  exact congrArg Campaign2.Product.observeResult equal

end Leanux.Proofs.WG.Progress.RecordSuffix
