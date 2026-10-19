import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeModel

/-! Projected budget-exit facts for the existing timer episode receipt. A done turn is distinct from global no-due, timer fairness or pending-work emptiness. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.Progress.RecordSuffix
open Leanux Leanux.WG Leanux.Env
open Leanux.Proofs.WG.TimerDiscipline

/-- The actual absent-device branch has no loop. Otherwise the captured supplied-record budget ends with a real done receipt; the Boolean control records whether work fired, not loop exhaustion. -/
def TimerEpisodeBudgetDone (records : List HiddenRecord) (receipt : OuterTimerEpisodeReceipt) : Prop :=
  if receipt.start.wg.device.isNone then
    receipt.budget=none ∧ receipt.turns=[]
  else
    receipt.budget=some (records.length+1) ∧
      ∃ front last, receipt.turns=front++[last] ∧ last.result=.done receipt.control

end Leanux.Proofs.WG.Progress.RecordSuffix
