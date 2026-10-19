import Leanux.Proofs.WG.TransmitSecurity.StagedObligationCarrier
import Leanux.Proofs.WG.TransmitSecurity.StagedAllocationOrigins
import Leanux.Proofs.WG.AuthenticatedEffects.AllocatedObligationMixedAllocation

/-! Allocation transfers selected entries to their exact native ordinals,
leaving every staged queue and other selected position unchanged. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects AllocatedObligation

theorem SelectedRecorded.assigned (before : SelectedRecorded history ledger)
    (takePosition batchPosition : Nat) :
    SelectedRecorded history (assignBatch takePosition batchPosition ledger) := by
  intro ticket position member
  obtain ⟨⟨old,status⟩,prior,equal⟩ := List.mem_map.mp (mem_pendingAt.mp member)
  have sameTicket : old = ticket := congrArg Prod.fst equal
  subst old
  cases status with
  | terminal outcome => simp [assignEntry] at equal
  | pending location =>
    cases location with
    | staged generation pid stamp => simp [assignEntry] at equal
    | allocated batch index => simp [assignEntry] at equal
    | selected actual =>
      by_cases chosen : actual = takePosition
      · simp [assignEntry,chosen] at equal
      · have same : actual = position := by simpa [assignEntry,chosen] using equal
        subst actual
        exact before ticket position (mem_pendingAt.mpr prior)

theorem QueueInv.assigned (before : QueueInv history ledger w) (takePosition batchPosition : Nat) :
    QueueInv history (assignBatch takePosition batchPosition ledger) w := by
  intro generation pid stamp
  rw [assignBatch_staged]
  exact before generation pid stamp

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
