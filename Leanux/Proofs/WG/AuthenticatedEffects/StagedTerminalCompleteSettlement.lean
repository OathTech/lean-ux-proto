import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteFacts

/-! Exact settlement transport for the converse. The same incoming tickets
are pending and distinct; the new terminal uses the current receipt position.
Older receipt counts remain equal, not merely included in the successor. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedProvenance

private theorem old_tickets (different : newOutcome ≠ oldOutcome)
    (pending : ∀ ticket ∈ chosen, ∀ status, (ticket,status) ∈ ledger → ∃ place, status = .pending place) :
    tickets oldOutcome (settle chosen newOutcome ledger) = tickets oldOutcome ledger := by
  classical
  induction ledger with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨ticket,status⟩ := entry
    have tail : ∀ ticket ∈ chosen, ∀ status, (ticket,status) ∈ rest → ∃ place, status = .pending place :=
      fun t member s found => pending t member s (List.mem_cons_of_mem _ found)
    have induction := ih tail
    cases status with
    | pending place =>
      by_cases selected : ticket ∈ chosen
      · simpa only [tickets,settle,List.map_cons,List.filterMap_cons,ite_eq_left selected,
          ite_eq_right different] using induction
      · simpa only [tickets,settle,List.map_cons,List.filterMap_cons,ite_eq_right selected] using induction
    | terminal actual =>
      have absent : ticket ∉ chosen := by
        intro selected
        obtain ⟨place,impossible⟩ := pending ticket selected (.terminal actual) (List.mem_cons_self ..)
        cases impossible
      by_cases equal : actual = oldOutcome
      · simpa only [tickets,settle,List.map_cons,List.filterMap_cons,ite_eq_right absent,
          ite_eq_left equal] using congrArg (List.cons ticket) induction
      · simpa only [tickets,settle,List.map_cons,List.filterMap_cons,ite_eq_right absent,
          ite_eq_right equal] using induction

private theorem fresh_tickets (fresh : ∀ ticket, (ticket,Status.terminal outcome) ∉ ledger) :
    tickets outcome (settle chosen outcome ledger) =
      (keys ledger).filter (fun ticket => decide (ticket ∈ chosen)) := by
  classical
  induction ledger with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨ticket,status⟩ := entry
    have tail : ∀ ticket, (ticket,Status.terminal outcome) ∉ rest :=
      fun t member => fresh t (List.mem_cons_of_mem _ member)
    have induction := ih tail
    by_cases selected : ticket ∈ chosen
    · simpa only [tickets,settle,keys,List.map_cons,List.filterMap_cons,ite_eq_left selected,
        ite_true,List.filter_cons,decide_eq_true selected] using congrArg (List.cons ticket) induction
    · cases status with
      | pending place =>
        simpa only [tickets,settle,keys,List.map_cons,List.filterMap_cons,ite_eq_right selected,
          List.filter_cons,decide_eq_false selected,Bool.false_eq_true,↓reduceIte] using induction
      | terminal actual =>
        have different : actual ≠ outcome := by
          intro equal
          exact fresh ticket (equal ▸ List.mem_cons_self ..)
        simpa only [tickets,settle,keys,List.map_cons,List.filterMap_cons,ite_eq_right selected,
          ite_eq_right different,List.filter_cons,decide_eq_false selected,Bool.false_eq_true,↓reduceIte] using induction

private theorem chosen_count {chosen : List Ticket} (valid : Valid domain ledger) (unique : chosen.Nodup)
    (resident : ∀ ticket ∈ chosen, ticket ∈ keys ledger) :
    ((keys ledger).filter (fun ticket => decide (ticket ∈ chosen))).length = chosen.length := by
  classical
  apply List.Perm.length_eq
  apply (List.perm_ext_iff_of_nodup ((valid.1.symm ▸ valid.2).filter _) unique).mpr
  intro ticket
  simp only [List.mem_filter,decide_eq_true_eq]
  exact ⟨And.right,fun member => ⟨resident ticket member,member⟩⟩

/-- A first-terminal cut accounts for exactly its distinct pending tickets,
with its native count supplied explicitly. Every old receipt keeps exactly
its former ticket set. This is local algebra, not initialized source coverage. -/
theorem Complete.settle_cut {chosen : List Ticket} (before : Complete history ledger)
    (valid : Valid domain ledger) (justified : Justified history ledger)
    (unique : chosen.Nodup)
    (pending : ∀ ticket ∈ chosen, ∃ place, (ticket,Status.pending place) ∈ ledger)
    (selected : demand history.length event = some requested)
    (count : chosen.length = requested.count) :
    Complete (history ++ [event]) (settle chosen requested.outcome ledger) := by
  classical
  have onlyPending : ∀ ticket ∈ chosen, ∀ status, (ticket,status) ∈ ledger → ∃ place, status = .pending place := by
    intro ticket member status found
    obtain ⟨place,there⟩ := pending ticket member
    exact ⟨place,unique_status (valid.1.symm ▸ valid.2) found there⟩
  have fresh : ∀ ticket, (ticket,Status.terminal requested.outcome) ∉ ledger := by
    intro ticket member
    have earlier := (justified.order member).2
    rw [demand_position selected] at earlier
    omega
  apply before.append_cut
  · intro oldOutcome earlier
    apply old_tickets (pending := onlyPending)
    intro equal
    have position := demand_position selected
    rw [equal] at position
    omega
  · intro actual actualSelected
    have same : actual = requested := Option.some.inj (actualSelected.symm.trans selected)
    subst actual
    rw [fresh_tickets fresh]
    rw [chosen_count valid unique]
    · exact count
    · intro ticket member
      obtain ⟨place,found⟩ := pending ticket member
      exact List.mem_map.mpr ⟨(ticket,Status.pending place),found,rfl⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
