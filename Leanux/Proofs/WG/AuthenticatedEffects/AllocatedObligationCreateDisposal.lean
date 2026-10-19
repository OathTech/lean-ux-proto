import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationFirstTerminalDebtDispose

/-! The refusal batch is an explicit list of native cells, each assigned to
a pending fixed ticket. A completed drop records the same allocation and the
actual branch-labelled source receipt, not merely an abstract terminal flag. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity HandshakeSecurity.StagedConservation
open TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations

def PendingBatch (history : List CausalJournal.Event) (ledger : Ledger) (items : List SkbId) : Prop :=
  ∀ id ∈ items, ∃ ticket position ordinal generation value,
    (ticket,Status.pending (.allocated position ordinal)) ∈ ledger ∧
    Origin history position ordinal generation id value

def Dropped (history : List CausalJournal.Event) (ledger : Ledger)
    (reason : Terminal.Reason) (id : SkbId) : Prop :=
  ∃ ticket position ordinal generation value cut, ∃ receipt : Terminal.Receipt,
    Origin history position ordinal generation id value ∧
    history[cut]? = some (.terminalDrop receipt) ∧ receipt.Valid ∧
    receipt.skb = id ∧ receipt.reason = reason ∧
    (ticket,Status.terminal (.disposed cut reason)) ∈ ledger

def AllDropped (history : List CausalJournal.Event) (ledger : Ledger)
    (reason : Terminal.Reason) (items : List SkbId) : Prop :=
  ∀ id ∈ items, Dropped history ledger reason id

abbrev free (reason : Terminal.Reason) (id : SkbId) : PrefixM CausalJournal.Event Unit :=
  Terminal.freeObserved CausalJournal.txEvent CausalJournal.txEvent?
    CausalJournal.Event.terminalDrop reason id

def loop (reason : Terminal.Reason) (items : List SkbId) : PrefixM CausalJournal.Event Unit :=
  for id in items do free reason id

end Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligation.CreateDisposal
