import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePublicationFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCompleteCarrier

/-! Paired entry-history framing at an actual failed focused native call. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity RetirementSecurity AllocatedObligation CausalJournal
open Staged.Obligations StagedTerminalComplete CompleteCarrier

/-- A failed focused native call extends the history of its retained entry
witness without asserting that the failed call returned a native world. -/
theorem focused_stopped (body : TxDisposition.Obs α)
    (before : Inv history ledger debts locals w.wg) (complete : Complete last ledger)
    (failed : runPrefix (QueueHandoff.focused body) w history = (.error stop,last)) :
    Accounted last ledger debts locals w.wg := by
  obtain ⟨suffix,extended,quiet⟩ := QueueHandoff.focused_quiet body w history
  change (runPrefix (QueueHandoff.focused body) w history).2 = _ at extended
  rw [failed] at extended
  change last = history ++ suffix at extended
  refine ⟨?_,complete⟩
  rw [extended]
  exact before.views suffix quiet rfl rfl rfl rfl rfl rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompleteSource
