import Leanux.Proofs.WG.Noise.PendingRunnerSource
import Leanux.Proofs.WG.Noise.ConfirmationOrderLabels

set_option autoImplicit false
namespace Leanux.Proofs.WG.Noise.ConfirmationOrder
open Leanux

/-- Successful completed consume receipts have distinct allocation identities
in the original initialized journal, including before a later outer Stop.
Device recreation cannot reuse the persistent allocation identity. -/
theorem initialized_distinct (trace : Runner.Trace) (placeholders : Bool) :
    ∃ ids, confirmationIds trace placeholders = .ok ids ∧ ids.Nodup := by
  have safe : PendingSession.HistorySafe (history trace placeholders) :=
    PendingRunner.executeTrace trace placeholders
  have distinct : (CounterConsume.confirmationLabels (history trace placeholders)).Nodup :=
    (List.pairwise_reverse.mp safe).imp (fun h => Ne.symm h)
  exact ⟨_,initialized_confirmationIds_labels trace placeholders,distinct⟩

end Leanux.Proofs.WG.Noise.ConfirmationOrder
