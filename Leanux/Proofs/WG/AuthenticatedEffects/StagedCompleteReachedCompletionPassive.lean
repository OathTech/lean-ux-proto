import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSendingScoped

/-! Matched passive cuts use the actual callback entry. Existing indexed
contracts supply only birth-domain preservation here; their existential saved
world is never used as source provenance. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch Staged.Obligations StagedTerminalComplete CompleteCarrier

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

structure PassiveStop (context : Context) (phase : Phase) (site : Site)
    (w : World) (history : List CausalJournal.Event) (ledger : Ledger) (debts : List CleanupDebt)
    (reason : Stop) (last : List CausalJournal.Event) : Prop where
  owned : Owned context phase history ledger debts w
  failed : runPrefix site.action w history = (.error reason,last)
  prefixHistory : history.IsPrefix last
  accounted : Accounted last ledger debts
    (⟨.selected,context.pid,phase.active context⟩ :: context.locals) w.wg

def passiveCut (context : Context) (phase : Phase) (site : Site)
    (w : World) (history : List CausalJournal.Event) (ledger : Ledger) (debts : List CleanupDebt) : Cut context :=
  ⟨ledger,debts,phase,w,history,.callback site⟩

theorem PassiveStop.valid (cut : PassiveStop context phase site w history ledger debts reason last) :
    (passiveCut context phase site w history ledger debts).Valid reason last :=
  ⟨cut.failed,cut.accounted⟩

theorem passive_failed
    (before : Owned context phase history ledger debts w)
    (checked : CompletionCuts.Ensures (fun h v => Owned context phase h ledger debts v)
      (IndexedStopped context ledger debts) site.action
      (fun _ h v => Owned context phase h ledger debts v))
    (paired : Complete (runPrefix site.action w history).2 ledger)
    (failed : runPrefix site.action w history = (.error reason,last)) :
    PassiveStop context phase site w history ledger debts reason last := by
  obtain ⟨suffix,grown,result⟩ := checked w history before
  rw [failed] at grown result paired
  dsimp only at grown
  obtain ⟨old⟩ := result
  have domain : births last = births history := old.sameBirths.trans
    (old.owned.domain.trans before.domain.symm)
  have quiet : ∀ event ∈ suffix, birthPackets event = [] := by
    apply domain_quiet (history := history)
    simpa only [← grown] using domain
  refine ⟨before,failed,⟨suffix,grown.symm⟩,?_,paired⟩
  rw [grown]
  exact Queued.Inv.history before.entry suffix quiet

theorem passive_returned
    (before : Owned context phase history ledger debts w)
    (checked : CompletionCuts.Ensures (fun h v => Owned context phase h ledger debts v)
      (IndexedStopped context ledger debts) action
      (fun _ h v => Owned context phase h ledger debts v))
    (paired : Complete (runPrefix action w history).2 ledger)
    (run : runPrefix action w history = (.ok (value,v),last)) :
    Owned context phase last ledger debts v ∧ Complete last ledger := by
  obtain ⟨_,_,result⟩ := checked w history before
  rw [run] at result paired
  exact ⟨result,paired⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Completion
