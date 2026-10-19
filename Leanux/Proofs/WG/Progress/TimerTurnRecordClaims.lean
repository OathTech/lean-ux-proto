import Leanux.Proofs.WG.Progress.TimerTurnRecordSource
import Leanux.Proofs.WG.Campaign2.Bridge

/-! Projected normal record effects for the exact timer-turn source.
Stopped final states, fuel adequacy and pending-unit emptiness are not asserted. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env Leanux.Proofs.Framing Leanux.Proofs.WG.TimerDiscipline

/-- On a normal original turn, all records are a suffix; an actual yield
strictly shortens it. This does not assume the enclosing completion guard. -/
theorem timerOuterTurn_record_strict (jPass : UInt64) (iteration : Nat)
    (control : Bool × Option UInt64) (records : List HiddenRecord) :
    Campaign2.Product.Ensures (timerOuterTurn jPass iteration control)
      (fun s=>s.ambient.hidden=some records)
      (fun result s=>Tail records s.ambient.hidden ∧
        ∀ next, result=ForInStep.yield next → StrictTail records s.ambient.hidden) := by
  intro before result after present run
  change before.ambient.hidden=some records at present
  refine ⟨(hoare_iff_run _ _ _).mp
    (timerOuterTurn_retains records jPass iteration control)
      before result after (present ▸ tail_self records) run,?_⟩
  intro next equal
  subst result
  exact timerOuterTurn_yield_strict jPass iteration control next records before after present run


end Leanux.Proofs.WG.Progress.RecordSuffix
