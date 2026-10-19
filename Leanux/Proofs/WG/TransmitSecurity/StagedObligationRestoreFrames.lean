import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeFrames
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationRestoreObserved
import Leanux.Proofs.WG.HandshakeSecurity.NonceRejectionFrames

/-! Exact native projected queue effects of whole-batch restoration. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins

/-- The actual restore prepends precisely its input batch to the current
resident queue at its current peer allocation; all other queues are equal. -/
theorem restore_receipt_views (r : HandshakeSecurity.StagedConservation.Restore.Receipt)
    (valid : r.Valid) :
    ∃ generation allocation queued, Packets.epoch r.run.before = some generation ∧
      Packets.epoch r.run.after = Packets.epoch r.run.before ∧
      stagedAt r.run.before r.pid = some (allocation,queued) ∧
      stagedAt r.run.after r.pid = some (allocation,r.packets ++ queued) ∧
      (∀ q, r.pid ≠ q → stagedAt r.run.after q = stagedAt r.run.before q) := by
  obtain ⟨d,p,device,resident,after,_⟩ :=
    HandshakeSecurity.NonceRejection.restoration r.pid r.packets r.run valid
  refine ⟨d.ifindex,p.internalId,p.staged,?_,?_,?_,?_,?_⟩
  · simp [Packets.epoch,device]
  · simp [Packets.epoch,device,after]
  · simp [stagedAt,device,resident]
  · simp [stagedAt,after]
  · intro q different
    simp [stagedAt,device,after,Std.TreeMap.getElem?_insert,different]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
