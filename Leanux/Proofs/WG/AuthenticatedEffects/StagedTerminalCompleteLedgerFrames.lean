import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteFacts
import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionLedger
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeTransfer

/-! Admission and pending-location transfers retain the exact old terminal
ticket lists. Physical cleanup also keeps the same ledger; no second terminal
is introduced by these frames. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedProvenance

theorem tickets_append_pending (fresh : List Ticket) :
    tickets outcome (ledger ++ fresh.map (fun ticket => (ticket,Status.pending place))) =
      tickets outcome ledger := by
  classical
  simp only [tickets,List.filterMap_append,List.filterMap_map,Function.comp_def]
  simp

theorem tickets_transfer (source target : Pending) :
    tickets outcome (transferLocation source target ledger) = tickets outcome ledger := by
  classical
  induction ledger with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨ticket,status⟩ := entry
    cases status with
    | pending place =>
      by_cases same : place = source <;>
        simpa only [tickets,transferLocation,List.map_cons,List.filterMap_cons,same,↓reduceIte] using ih
    | terminal actual =>
      by_cases same : actual = outcome
      · simpa only [tickets,transferLocation,List.map_cons,List.filterMap_cons,ite_eq_left same] using
          congrArg (List.cons ticket) ih
      · simpa only [tickets,transferLocation,List.map_cons,List.filterMap_cons,ite_eq_right same] using ih

theorem Complete.same_terminals (before : Complete history ledger)
    (same : ∀ outcome, tickets outcome afterLedger = tickets outcome ledger) : Complete history afterLedger :=
  scan_transfer before (fun outcome _ => same outcome)

theorem Complete.admitted (before : Complete history ledger) (position : Nat)
    (place : Pending) (packets : List Packet) :
    Complete history (StagedAdmission.appendBirths ledger position place packets) := by
  apply before.same_terminals
  intro outcome
  exact tickets_append_pending _

theorem Complete.transferred (before : Complete history ledger) (source target : Pending) :
    Complete history (transferLocation source target ledger) :=
  before.same_terminals (fun _ => tickets_transfer source target)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
