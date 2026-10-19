import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixDisposalHistory
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSendLoop

/-! Prefix certificates strengthen the result-aware completion contract without
forgetting its indexed returned cursor or stopped source frontier. These are
logical journal prefixes; native reached-cut correspondence is independent. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations CompleteCarrier

abbrev AccountSafe (Safe : List CausalJournal.Event → Prop) : Prop :=
  ∀ h ledger debts locals w, Accounted h ledger debts locals w → Safe h

def Checked (P : List E → World → Prop) (Safe : List E → Prop)
    (stopped : Stop → List E → Prop) (action : PrefixM E α)
    (Q : α → List E → World → Prop) : Prop :=
  CompletionCuts.Ensures (fun h w => P h w ∧ All Safe h)
    (fun reason h => stopped reason h ∧ All Safe h) action
    (fun value h w => Q value h w ∧ All Safe h)

theorem Checked.of_cuts {Safe : List E → Prop}
    (endpoint : CompletionCuts.Ensures P stopped action Q)
    (cuts : ∀ w h, P h w → ∃ suffix,
      (runPrefix action w h).2 = h ++ suffix ∧ Cuts Safe h suffix) :
    Checked P Safe stopped action Q := by
  intro w h before
  obtain ⟨suffix,grown,result⟩ := endpoint w h before.1
  obtain ⟨added,extended,certified⟩ := cuts w h before.1
  have all : All Safe (runPrefix action w h).2 := by rw [extended]; exact before.2.append certified
  refine ⟨suffix,grown,?_⟩
  cases run : (runPrefix action w h).1 with
  | error reason => exact ⟨by simpa only [run] using result,all⟩
  | ok out => exact ⟨by simpa only [run] using result,all⟩

theorem Checked.bind {Safe : List E → Prop} (first : Checked P Safe stopped action Q)
    (next : ∀ value, Checked (Q value) Safe stopped (continuation value) R) :
    Checked P Safe stopped (action >>= continuation) R :=
  CompletionCuts.Ensures.bind first next

variable {Safe : List CausalJournal.Event → Prop}

theorem owned_safe (accountSafe : AccountSafe Safe)
    (owned : Owned context phase h ledger debts w)
    (complete : StagedTerminalComplete.Complete h ledger) : Safe h :=
  accountSafe h ledger debts _ w.wg ⟨owned.entry,complete⟩

theorem quiet_cuts (accountSafe : AccountSafe Safe)
    (owned : Owned context phase h ledger debts w)
    (complete : StagedTerminalComplete.Complete h ledger)
    (quiet : (h ++ suffix).filterMap ledgerEvent? = h.filterMap ledgerEvent?) :
    Cuts Safe h suffix := by
  have empty : suffix.filterMap ledgerEvent? = [] := by
    rw [List.filterMap_append] at quiet
    exact List.append_cancel_left (as := h.filterMap ledgerEvent?)
      (by simpa only [List.append_nil] using quiet)
  exact Disposal.quiet_cuts Safe (fun l k v => accountSafe k l _ _ v)
    ⟨owned.entry,complete⟩ suffix
    (fun event member => ledger_quiet_birth event (List.filterMap_eq_nil_iff.mp empty event member))
    (fun event member => Converse.ledger_quiet event (List.filterMap_eq_nil_iff.mp empty event member))

theorem quiet_output (accountSafe : AccountSafe Safe)
    (owned : Owned context phase h ledger debts w)
    (complete : StagedTerminalComplete.Complete h ledger)
    (appends : Appends action) (quiet : HistoryFrame ledgerEvent? action) :
    ∃ suffix, (runPrefix action w h).2 = h ++ suffix ∧ Cuts Safe h suffix := by
  obtain ⟨suffix,grown⟩ := appends w h
  exact ⟨suffix,grown,quiet_cuts accountSafe owned complete (grown ▸ quiet w h)⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
