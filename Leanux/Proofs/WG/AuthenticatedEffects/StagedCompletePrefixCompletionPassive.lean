import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixCompletionLoop
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompletePrefixFixedHistory
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationCompletionCompleteSequence

/-! A passive callback retains the old indexed ledger and proves completeness
on that same ledger. Restricting that scan and the unchanged birth domain
certifies each logical prefix, without rolling a settled ledger backward. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete
variable {Safe : List CausalJournal.Event → Prop}

private theorem birthsFrom_empty (empty : birthsFrom start suffix = []) :
    ∀ event ∈ suffix, birthPackets event = [] := by
  induction suffix generalizing start with
  | nil => simp
  | cons head rest ih =>
    simp only [birthsFrom,List.append_eq_nil_iff] at empty
    have headEmpty : birthPackets head = [] := by
      cases packets : birthPackets head with
      | nil => rfl
      | cons packet more => simp [packets,Staged.Origins.freshTickets] at empty
    intro event member
    rcases List.mem_cons.mp member with rfl | inside
    · exact headEmpty
    · exact ih empty.2 event inside

private theorem domain_quiet (same : births (history ++ suffix) = births history) :
    ∀ event ∈ suffix, birthPackets event = [] := by
  change birthsFrom 0 (history ++ suffix) = birthsFrom 0 history at same
  rw [birthsFrom_append] at same
  have empty : birthsFrom (0 + history.length) suffix = [] :=
    List.append_cancel_left (by simpa only [List.append_nil] using same)
  exact birthsFrom_empty empty

theorem indexed_passive_cuts (accountSafe : AccountSafe Safe)
    (before : Owned context phase history ledger debts w) (complete : Complete history ledger)
    (checked : CompletionCuts.Ensures (fun h v => Owned context phase h ledger debts v)
      (IndexedStopped context ledger debts) action
      (fun _ h v => Owned context phase h ledger debts v))
    (paired : Complete (runPrefix action w history).2 ledger) :
    ∃ suffix, (runPrefix action w history).2 = history ++ suffix ∧ Cuts Safe history suffix := by
  obtain ⟨suffix,grown,result⟩ := checked w history before
  have domain : births (runPrefix action w history).2 = context.births := by
    cases run : (runPrefix action w history).1 with
    | error reason =>
      have stopped : IndexedStopped context ledger debts reason (runPrefix action w history).2 := by
        simpa only [run] using result
      obtain ⟨frontier⟩ := stopped
      exact frontier.sameBirths.trans frontier.owned.domain
    | ok out =>
      have after : Owned context phase (runPrefix action w history).2 ledger debts out.2 := by
        simpa only [run] using result
      exact after.domain
  rw [grown] at domain paired
  exact ⟨suffix,grown,FixedHistory.cuts Safe (fun l h g => accountSafe h l _ _ g)
    ⟨before.entry,complete⟩ (domain_quiet (domain.trans before.domain.symm)) paired⟩

theorem sending_passive (context : Context) (initial : Ledger) (original : List CleanupDebt)
    (remaining : List SkbId) (action : PrefixM CausalJournal.Event α) (accountSafe : AccountSafe Safe)
    (checked : ∀ ledger debts,
      CompletionCuts.Ensures (fun h w => Owned context (.sending remaining) h ledger debts w)
        (IndexedStopped context ledger debts) action
        (fun _ h w => Owned context (.sending remaining) h ledger debts w))
    (preserves : ∀ ledger debts h w, Owned context (.sending remaining) h ledger debts w →
      Complete h ledger → Complete (runPrefix action w h).2 ledger) :
    Checked (Converse.Sending context initial original remaining) Safe (Converse.SendingStopped context initial original)
      action (fun _ => Converse.Sending context initial original remaining) := by
  apply Checked.of_cuts
  · intro w h before
    obtain ⟨ledger,debts,trace,owned,localDebts,complete⟩ := before
    obtain ⟨suffix,grown,result⟩ := checked ledger debts w h owned
    have paired := preserves ledger debts h w owned complete
    refine ⟨suffix,grown,?_⟩
    cases run : (runPrefix action w h).1 with
    | error reason => exact ⟨ledger,debts,trace,(by simpa only [run] using result),paired⟩
    | ok out => exact ⟨ledger,debts,trace,(by simpa only [run] using result),localDebts,paired⟩
  · intro w h before
    obtain ⟨ledger,debts,_,owned,_,complete⟩ := before
    exact indexed_passive_cuts accountSafe owned complete (checked ledger debts)
      (preserves ledger debts h w owned complete)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.CompletePrefix.Completion
