import Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalCompleteLedgerFrames
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationInjectiveAssignment

/-! Native batch assignment changes only selected pending locations. Its
exact terminal-ticket filter is unchanged, unlike arbitrary ledger Step. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
open Leanux Leanux.WG
open TransmitSecurity TransmitSecurity.Staged.Obligations AllocatedObligation

theorem tickets_assign_entries (takePosition batchPosition : Nat) (selected : List Staged.Origins.Ticket) :
    tickets outcome (ledger.map (assignEntry takePosition batchPosition selected)) = tickets outcome ledger := by
  classical
  induction ledger with
  | nil => rfl
  | cons entry rest ih =>
    obtain ⟨ticket,status⟩ := entry
    cases status with
    | pending location =>
      cases location with
      | staged => simpa only [List.map_cons,assignEntry,tickets,List.filterMap_cons] using ih
      | allocated => simpa only [List.map_cons,assignEntry,tickets,List.filterMap_cons] using ih
      | selected actual =>
        by_cases same : actual = takePosition <;>
          simpa only [List.map_cons,assignEntry,same,↓reduceIte,tickets,List.filterMap_cons] using ih
    | terminal actual =>
      by_cases same : actual = outcome
      · simpa only [List.map_cons,assignEntry,tickets,List.filterMap_cons,ite_eq_left same] using
          congrArg (List.cons ticket) ih
      · simpa only [List.map_cons,assignEntry,tickets,List.filterMap_cons,ite_eq_right same] using ih

theorem Complete.assigned (before : Complete history ledger) (takePosition batchPosition : Nat) :
    Complete history (assignBatch takePosition batchPosition ledger) :=
  before.same_terminals (fun _ => tickets_assign_entries takePosition batchPosition _)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedTerminalComplete
