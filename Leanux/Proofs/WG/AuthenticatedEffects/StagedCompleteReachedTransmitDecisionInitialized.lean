import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitInitialized
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTransmitFrontPath

/-! The original routed-send invocation reaches the front's fixed guard
prefix before release, overflow or splice. Its ledger is derived from the
initialized caller and is retained at the actual selected native state. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open Queues Queues.RxCredits TransmitSecurity CausalJournal RunnerSource

def Caller.decisionPrefix (caller : Caller trace placeholders operationIndex world history) :
    WGPrefix Event (Except Int Transmit.Front.Choice) := do
  emitStatePrefix (.transmitInput caller.input)
  Transmit.Front.decisionPrefix caller.input

theorem Caller.decision_run (caller : Caller trace placeholders operationIndex world history)
    (selected : Transmit.Front.Selected caller.input (Transmit.inputHistory caller.input caller.events)
      caller.entered.wg caller.entered.ambient decision v b) :
    runPrefix (liftWGObserver caller.decisionPrefix) caller.entered caller.events=
      (.ok (.ok decision,caller.updated v b),Transmit.inputHistory caller.input caller.events) := by
  rw [liftWGObserver_run]
  change ((runWGPrefix _ _ _ _).1.map _,(runWGPrefix _ _ _ _).2)=_
  unfold Caller.decisionPrefix
  rw [selected.input_literal]
  rfl

theorem Caller.decision_accounted (caller : Caller trace placeholders operationIndex world history)
    (selected : Transmit.Front.Selected caller.input (Transmit.inputHistory caller.input caller.events)
      caller.entered.wg caller.entered.ambient decision v b) :
    ∃ ledger, CompleteConsequences.Cut (Transmit.inputHistory caller.input caller.events)
      ledger [] [] (caller.updated v b).wg := by
  obtain ⟨ledger,before⟩ := caller.entry.1
  have marked : CompleteCarrier.Accounted (Transmit.inputHistory caller.input caller.events)
      ledger [] [] caller.entered.wg :=
    before.append_quiet [.transmitInput caller.input]
      (by intro event member; cases List.mem_singleton.mp member; rfl)
      (by intro event member; cases List.mem_singleton.mp member; intro position; rfl)
  exact ⟨ledger,CompleteConsequences.accounted (selected.accounted marked)⟩

/-- The selected residual is the original front body at this same cut;
the eventual routed receipt remains outside that body. -/
theorem Caller.decision_body_continuation (caller : Caller trace placeholders operationIndex world history)
    (selected : Transmit.Front.Selected caller.input (Transmit.inputHistory caller.input caller.events)
      caller.entered.wg caller.entered.ambient decision v b) :
    runWGPrefix (Transmit.body caller.input) caller.entered.wg caller.entered.ambient
      (Transmit.inputHistory caller.input caller.events)=
      runWGPrefix (Transmit.Front.resolve caller.input decision) v b
        (Transmit.inputHistory caller.input caller.events) := selected.continuation

theorem Caller.front_failed (caller : Caller trace placeholders operationIndex world history)
    (stopped : Transmit.Stopped caller.input caller.events caller.entered.wg caller.entered.ambient reason last) :
    (Transmit.Front.PrefixFailure caller.input (Transmit.inputHistory caller.input caller.events)
      caller.entered.wg caller.entered.ambient reason ∧
      last=Transmit.inputHistory caller.input caller.events) ∨
    (∃ ledger decision v b,
      Transmit.Front.Selected caller.input (Transmit.inputHistory caller.input caller.events)
        caller.entered.wg caller.entered.ambient decision v b ∧
      CompleteCarrier.Accounted (Transmit.inputHistory caller.input caller.events) ledger [] [] v ∧
      runWGPrefix (Transmit.Front.resolve caller.input decision) v b
        (Transmit.inputHistory caller.input caller.events)=(.error reason,last)) := by
  obtain ⟨ledger,before⟩ := caller.entry.1
  rcases Transmit.Front.stopped_classify before stopped with prefixFailure | residual
  · exact Or.inl prefixFailure
  · obtain ⟨decision,v,b,selected,accounted,failed⟩ := residual
    exact Or.inr ⟨ledger,decision,v,b,selected,accounted,failed⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
