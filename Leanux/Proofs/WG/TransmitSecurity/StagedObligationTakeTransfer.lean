import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSettlement

/-! Transfer a complete pending location without changing ticket identities,
ledger order, births or any prior terminal outcome. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins

def transferLocation (source target : Pending) (ledger : Ledger) : Ledger :=
  ledger.map fun entry => (entry.1,match entry.2 with
    | .pending actual => if actual = source then .pending target else entry.2
    | .terminal _ => entry.2)

def pendingPair (left right : Pending) (ledger : Ledger) : List Ticket :=
  ledger.filterMap fun entry => match entry.2 with
    | .pending actual => if actual = left ∨ actual = right then some entry.1 else none
    | .terminal _ => none

theorem transferLocation_step (source target : Pending) (ledger : Ledger) :
    Step ledger (transferLocation source target ledger) := by
  induction ledger with
  | nil => exact .nil
  | cons entry rest ih =>
    apply Step.cons entry.1
    · cases status : entry.2 with
      | terminal outcome => exact .retain _
      | pending actual =>
        by_cases same : actual = source
        · simp only [same,ite_true]
          exact .transfer _ _
        · simp only [same,ite_false]
          exact .retain _
    · exact ih

theorem pendingAt_transfer_source (different : source ≠ target) (ledger : Ledger) :
    pendingAt source (transferLocation source target ledger) = [] := by
  induction ledger with
  | nil => rfl
  | cons entry rest ih =>
    simp only [transferLocation,pendingAt,List.filterMap_map] at ih
    rcases entry with ⟨ticket,status⟩
    cases status with
    | terminal outcome => simpa [transferLocation,pendingAt] using ih
    | pending actual =>
      by_cases same : actual = source
      · subst actual
        simp [transferLocation,pendingAt,Ne.symm different,ih]
      · simp [transferLocation,pendingAt,same,ih]

theorem pendingAt_transfer_other (notSource : other ≠ source) (notTarget : other ≠ target)
    (ledger : Ledger) :
    pendingAt other (transferLocation source target ledger) = pendingAt other ledger := by
  induction ledger with
  | nil => rfl
  | cons entry rest ih =>
    simp only [transferLocation,pendingAt,List.filterMap_map] at ih
    rcases entry with ⟨ticket,status⟩
    cases status with
    | terminal outcome => simpa [transferLocation,pendingAt] using ih
    | pending actual =>
      by_cases same : actual = source
      · subst actual
        simp [transferLocation,pendingAt,Ne.symm notSource,Ne.symm notTarget,ih]
      · by_cases located : actual = other <;> simp [transferLocation,pendingAt,same,located,notSource,ih]

theorem pendingAt_transfer_target (source target : Pending) (ledger : Ledger) :
    pendingAt target (transferLocation source target ledger) = pendingPair source target ledger := by
  induction ledger with
  | nil => rfl
  | cons entry rest ih =>
    simp only [transferLocation,pendingAt,List.filterMap_map] at ih
    rcases entry with ⟨ticket,status⟩
    cases status with
    | terminal outcome => simpa [transferLocation,pendingAt,pendingPair] using ih
    | pending actual =>
      by_cases first : actual = source <;> by_cases second : actual = target <;>
        simp [transferLocation,pendingAt,pendingPair,first,second,ih]

theorem pendingPair_empty_right (empty : pendingAt target ledger = []) :
    pendingPair source target ledger = pendingAt source ledger := by
  induction ledger with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨ticket,status⟩
    cases status with
    | terminal outcome =>
      exact ih (by simpa [pendingAt] using empty)
    | pending actual =>
      by_cases second : actual = target
      · simp [pendingAt,second] at empty
      · have tail : pendingAt target rest = [] := by simpa [pendingAt,second] using empty
        have rest := ih tail
        simp only [pendingPair,pendingAt] at rest
        by_cases first : actual = source <;> simp [pendingPair,pendingAt,first,second,rest]

theorem pendingAt_transfer_unused (empty : pendingAt target ledger = []) :
    pendingAt target (transferLocation source target ledger) = pendingAt source ledger := by
  rw [pendingAt_transfer_target,pendingPair_empty_right empty]

/-- The same existing ticket is pending at the new location. No new birth or
terminal result is introduced by the transfer. -/
theorem transferLocation_member (member : ticket ∈ pendingAt source ledger) :
    (ticket,Status.pending target) ∈ transferLocation source target ledger := by
  apply List.mem_map.mpr
  refine ⟨(ticket,Status.pending source),mem_pendingAt.mp member,?_⟩
  simp

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
