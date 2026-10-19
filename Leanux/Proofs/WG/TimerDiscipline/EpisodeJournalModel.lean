import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeModel

/-! Projected receipts for each actual runTimers invocation. Successful outcomes carry the original complete wheel episode; failed calls retain their exact Stop. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
open Leanux
structure Receipt where
  bound : UInt64
  before : Campaign2.Product.Snapshot
  outcome : Campaign2.Product.Outcome (OuterTimerEpisodeReceipt × Bool)

def OutcomeFacts (receipt : Receipt) : Prop :=
  match receipt.outcome with
  | .error _ => True
  | .ok ((episode,result),final) =>
    OuterTimerEpisodeValid receipt.bound receipt.before episode result final


end Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
