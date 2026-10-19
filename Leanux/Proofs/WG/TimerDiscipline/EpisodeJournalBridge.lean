import Leanux.Proofs.WG.TimerDiscipline.EpisodeJournalModel
import Leanux.Proofs.WG.TimerDiscipline.OuterEpisodeClaims

/-! Native source evidence hidden behind the projected receipt predicate. This does not give a final state or completed turn list for an interrupted episode. -/
set_option autoImplicit false
namespace Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
open Leanux
def SourceReceipt (receipt : Receipt) : Prop :=
  ∃ entry : World, receipt.before = Campaign2.Product.snapshot entry ∧
    receipt.outcome = Campaign2.Product.observeResult ((observedRunTimersEpisode receipt.bound).run entry)

def Valid (receipt : Receipt) : Prop := SourceReceipt receipt ∧ OutcomeFacts receipt

def ValidHistory (history : List Receipt) : Prop := ∀ receipt ∈ history, Valid receipt


end Leanux.Proofs.WG.TimerDiscipline.EpisodeJournal
