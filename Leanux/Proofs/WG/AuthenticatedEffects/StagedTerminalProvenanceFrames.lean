import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalProvenance
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionLedger
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeTransfer

/-! Admission and ownership transfer cannot manufacture terminal evidence.
Settlement requires evidence at its actual receipt, while the ordinary Step
premise separately prevents replacing an already recorded first terminal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open AllocatedObligation CausalJournal

theorem Justified.empty (history : List Event) : Justified history [] := by
  intro _ _ member
  cases member

theorem Justified.map (before : Justified history ledger) (f : Ticket × Status → Ticket × Status)
    (reflects : ∀ entry ticket outcome, f entry = (ticket,Status.terminal outcome) →
      entry = (ticket,Status.terminal outcome)) : Justified history (ledger.map f) := by
  intro ticket outcome member
  obtain ⟨entry,inside,equal⟩ := List.mem_map.mp member
  exact before ticket outcome (reflects entry ticket outcome equal ▸ inside)

theorem Justified.transfer (before : Justified history ledger) (source target : Pending) :
    Justified history (transferLocation source target ledger) := by
  apply before.map _
  rintro ⟨ticket,status⟩ other outcome equal
  cases status with
  | terminal old => exact equal
  | pending location =>
    by_cases same : location = source <;> simp [same] at equal

theorem Justified.assigned (before : Justified history ledger) (takePosition batchPosition : Nat) :
    Justified history (assignBatch takePosition batchPosition ledger) := by
  apply before.map _
  rintro ⟨ticket,status⟩ other outcome equal
  cases status with
  | terminal old => exact equal
  | pending location =>
    cases location with
    | staged => simp [assignEntry] at equal
    | allocated => simp [assignEntry] at equal
    | selected position =>
      by_cases same : position = takePosition <;> simp [assignEntry,same] at equal

theorem Justified.admitted (before : Justified history ledger) (position : Nat)
    (location : Pending) (packets : List Packet) :
    Justified history (StagedAdmission.appendBirths ledger position location packets) := by
  intro ticket outcome member
  rcases List.mem_append.mp member with old | fresh
  · exact before ticket outcome old
  · obtain ⟨_,_,equal⟩ := List.mem_map.mp fresh
    cases equal

theorem Justified.settled (before : Justified history ledger)
    (evidence : ∀ ticket ∈ selected, Evidence history ticket outcome) :
    Justified history (settle selected outcome ledger) := by
  intro ticket terminal member
  obtain ⟨⟨old,status⟩,inside,equal⟩ := List.mem_map.mp member
  have same : old = ticket := congrArg Prod.fst equal
  subst old
  by_cases chosen : ticket ∈ selected
  · have result : outcome = terminal := by
      simpa only [ite_eq_left chosen,Prod.mk.injEq,Status.terminal.injEq,true_and] using equal
    subst terminal
    exact evidence ticket chosen
  · have result : status = .terminal terminal := by
      simpa only [ite_eq_right chosen,Prod.mk.injEq,true_and] using equal
    subst status
    exact before ticket terminal inside

/-- Local source settlement needs the incoming pending occurrence and its
same-cut evidence. It yields Step as well as provenance, so cleanup cannot
replace an older terminal with a newer receipt. -/
theorem settle_at (valid : Valid domain ledger) (before : Justified history ledger)
    (chosen : ∀ ticket ∈ selected, ticket ∈ pendingAt location ledger)
    (atCut : ∀ ticket ∈ selected, At history event ticket outcome) :
    Staged.Obligations.Step ledger (settle selected outcome ledger) ∧
      Justified (history ++ [event]) (settle selected outcome ledger) :=
  ⟨settle_pending (valid.1.symm ▸ valid.2) chosen,
    (before.append [event]).settled (fun ticket member => Evidence.here (atCut ticket member))⟩

theorem AllocationLinks.settled (before : AllocationLinks history ledger)
    (selected : List Ticket) (outcome : Staged.Obligations.Terminal) :
    AllocationLinks history (settle selected outcome ledger) :=
  fun ticket batch ordinal member => before ticket batch ordinal (pending_after_settle _ _ member).1

end Leanux.Proofs.WG.AuthenticatedEffects.StagedProvenance
