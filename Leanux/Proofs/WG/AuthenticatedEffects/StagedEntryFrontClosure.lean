import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryCarrier
import Leanux.Proofs.WG.AuthenticatedEffects.StagedEntryOwnershipObserved

/-! No selected ticket remains across a whole front: the front only settles
staged tickets or appends new staged admissions. It never takes a staging
queue or allocates encrypted packets. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
open Leanux Leanux.WG Leanux.Proofs.Logged
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal StagedAdmission.Front

theorem checkpoint_no_selected (cut : Checkpoint entry history ledger snapshot)
    (before : NoSelected entry.ledger) : NoSelected ledger := by
  cases cut with
  | initial => exact before
  | nonfinal => exact before
  | released => exact before.settled _ _
  | trimmed => exact before.settled _ _

theorem normal_no_selected (normal : Normal entry input r history ledger)
    (before : NoSelected entry.ledger) : NoSelected ledger := by
  obtain ⟨prior,snapshot,cut,after⟩ := normal.2.2.2.2
  cases result : r.value with
  | error code =>
    rw [result] at after
    rw [after.1]
    exact checkpoint_no_selected cut before
  | ok pid =>
    rw [result] at after
    obtain ⟨w,a,generation,stamp,_,_,rfl⟩ := after
    exact (checkpoint_no_selected cut before).admitted _ _ _ _ _

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry
