import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete

/-! Pure terminal-converse algebra. Passive history transport requires the
terminal selector to be empty, and changed ledgers retain every older demand
before a newly observed cut is introduced. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedProvenance

theorem demand_position (selected : demand position event = some requested) :
    terminalPosition requested.outcome = position := by
  cases event <;> simp only [demand] at selected
  all_goals try (cases selected <;> rfl)
  case old value => cases value <;> cases selected <;> rfl
  case stagedDisposal value =>
    cases value
    all_goals try (cases selected <;> rfl)
    rename_i peer receipt
    cases result : receipt.value <;> simp only [result,Option.map_none,Option.map_some] at selected
    · cases selected
    · cases selected; rfl
  case sendResult receipt =>
    split at selected
    · cases selected
    · cases selected; rfl

theorem mem_tickets : ticket ∈ tickets outcome ledger ↔ (ticket,Status.terminal outcome) ∈ ledger := by
  classical
  simp only [tickets,List.mem_filterMap]
  constructor
  · rintro ⟨⟨other,status⟩,member,found⟩
    cases status with
    | pending place => cases found
    | terminal actual =>
      change (if actual = outcome then some other else none) = some ticket at found
      by_cases same : actual = outcome
      · rw [ite_eq_left same] at found
        cases found
        simpa only [same] using member
      · rw [ite_eq_right same] at found
        cases found
  · intro member
    exact ⟨(ticket,Status.terminal outcome),member,by simp⟩

theorem scan_append : Scan offset (history ++ suffix) ledger ↔
    Scan offset history ledger ∧ Scan (offset+history.length) suffix ledger := by
  induction history generalizing offset with
  | nil => simp [Scan]
  | cons event rest ih =>
    simp only [List.cons_append,Scan,ih,List.length_cons]
    have add : offset+1+rest.length = offset+(rest.length+1) := by omega
    rw [add]
    exact and_assoc.symm

theorem scan_quiet (quiet : ∀ event ∈ history, Quiet event) : Scan offset history ledger := by
  induction history generalizing offset with
  | nil => trivial
  | cons event rest ih =>
    refine ⟨?_,ih (fun e member => quiet e (List.mem_cons_of_mem _ member))⟩
    intro requested selected
    rw [quiet event (List.mem_cons_self ..) offset] at selected
    cases selected

theorem Complete.empty (ledger : Ledger) : Complete [] ledger := trivial

theorem Complete.append_quiet (before : Complete history ledger)
    (quiet : ∀ event ∈ suffix, Quiet event) : Complete (history ++ suffix) ledger :=
  scan_append.mpr ⟨before,scan_quiet quiet⟩

theorem scan_transfer (before : Scan offset history ledger)
    (same : ∀ outcome, terminalPosition outcome < offset+history.length →
      tickets outcome afterLedger = tickets outcome ledger) : Scan offset history afterLedger := by
  induction history generalizing offset with
  | nil => trivial
  | cons event rest ih =>
    refine ⟨?_,ih before.2 ?_⟩
    · intro requested selected
      rw [same requested.outcome (by rw [demand_position selected]; simp)]
      exact before.1 requested selected
    · intro outcome bound
      apply same outcome
      simp only [List.length_cons] at *
      omega

/-- Exact old-ticket preservation plus the new cut's cardinality extends the
converse. A bare Step is deliberately insufficient: it permits settling a new
ticket to an older label and would not preserve an exact earlier count. -/
theorem Complete.append_cut (before : Complete history ledger)
    (same : ∀ outcome, terminalPosition outcome < history.length →
      tickets outcome afterLedger = tickets outcome ledger)
    (cut : Satisfied history.length event afterLedger) : Complete (history ++ [event]) afterLedger := by
  apply scan_append.mpr
  exact ⟨scan_transfer before (by simpa only [Nat.zero_add] using same),(by simpa only [Nat.zero_add] using cut),True.intro⟩

theorem scan_at (before : Scan offset history ledger) (selected : history[position]? = some event) :
    Satisfied (offset+position) event ledger := by
  induction history generalizing offset position with
  | nil => simp at selected
  | cons head rest ih =>
    cases position with
    | zero => cases selected; simpa only [Nat.add_zero] using before.1
    | succ n =>
      have result := ih before.2 selected (offset := offset+1)
      simpa only [Nat.add_assoc,Nat.add_comm 1 n] using result

theorem Complete.at (before : Complete history ledger) (selected : history[position]? = some event) :
    Satisfied position event ledger := by simpa only [Nat.zero_add] using scan_at before selected

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
