import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitDecisionInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitInitializedReceipt
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontResidualReceipt

/-! The initialized routed call supplies the entry account for its original
overflow loop. Silent removals keep that same ticket cohort; the completed
overflow and routed receipts settle only their own actual source runs. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource Lifetimes
variable {packets : List WG.Packet}

theorem Caller.selected_account
    (caller : Caller trace placeholders operationIndex world history)
    (selected : Transmit.Front.Selected caller.input (Transmit.inputHistory caller.input caller.events)
      caller.entered.wg caller.entered.ambient decision u c) :
    ∃ ledger, CompleteCarrier.Accounted (Transmit.inputHistory caller.input caller.events) ledger [] [] u := by
  obtain ⟨ledger,before⟩ := caller.entry.1
  have marked : CompleteCarrier.Accounted (Transmit.inputHistory caller.input caller.events)
      ledger [] [] caller.entered.wg :=
    before.append_quiet [.transmitInput caller.input]
      (by intro event member; cases List.mem_singleton.mp member; rfl)
      (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)
  exact ⟨ledger,selected.accounted marked⟩

/-- Each yielded trim prefix uses the account derived at this same selected
front. No account is asserted after a queue mutation but before its receipt. -/
theorem Caller.trim_cut
    (caller : Caller trace placeholders operationIndex world history)
    (selected : Transmit.Front.Selected caller.input (Transmit.inputHistory caller.input caller.events)
      caller.entered.wg caller.entered.ambient (.splice pid packets) u c)
    (read : ∃ d p, u.dev=some d ∧ d.peers[pid]?=some p)
    (walk : Transmit.Front.Residual.Yields pid u c count v b) :
    ∃ ledger, Transmit.Front.Residual.TrimCut (Transmit.inputHistory caller.input caller.events)
      ledger [] [] pid u c count v b := by
  obtain ⟨ledger,before⟩ := caller.selected_account selected
  exact ⟨ledger,before,walk,read⟩

theorem Caller.overflow_accounted
    (caller : Caller trace placeholders operationIndex world history)
    (selected : Transmit.Front.Selected caller.input (Transmit.inputHistory caller.input caller.events)
      caller.entered.wg caller.entered.ambient (.splice pid packets) u c)
    (trim : ((xmitTrim pid).run u).run c=.ok (((),v),b)) :
    ∃ ledger, CompleteConsequences.Cut
      (Transmit.Front.Residual.overflowHistory pid u v c b (Transmit.inputHistory caller.input caller.events))
      ledger [] [] (caller.updated v b).wg := by
  obtain ⟨ledger,before⟩ := caller.selected_account selected
  obtain ⟨after,accounted,_,_⟩ := Transmit.Front.Residual.trim_account before trim
  exact ⟨after,CompleteConsequences.accounted accounted⟩

/-- The pre-birth native state and the later receipt share the actual
selected splice; all runner callbacks remain in the original continuation. -/
theorem Caller.splice_path
    (caller : Caller trace placeholders operationIndex world history)
    (selected : Transmit.Front.Selected caller.input (Transmit.inputHistory caller.input caller.events)
      caller.entered.wg caller.entered.ambient (.splice pid packets) u c)
    (trim : ((xmitTrim pid).run u).run c=.ok (((),v),b))
    (spliced : ((xmitSplice pid packets).run v).run b=.ok (((),q),z)) :
    Transmit.Path caller.input caller.events caller.entered.wg caller.entered.ambient (.ok pid) q z
      (Transmit.Front.Residual.overflowHistory pid u v c b (Transmit.inputHistory caller.input caller.events)) :=
  Transmit.Front.Residual.selected_splice selected trim spliced

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
