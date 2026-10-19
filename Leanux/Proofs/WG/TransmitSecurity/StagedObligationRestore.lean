import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeTransfer
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationRestoreFrames

/-! Whole-batch restoration moves the same selected tickets back to staged
ownership. A nonempty destination requires its explicit ledger order to agree
with the native prepend; the empty destination specialization derives it. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins
open AuthenticatedEffects.CausalJournal

theorem restore_step (r : HandshakeSecurity.StagedConservation.Restore.Receipt)
    (run : r.Valid) (valid : Valid births ledger)
    (before : QueueInv history ledger r.run.before)
    (epoch : Packets.epoch r.run.before = some generation)
    (resident : stagedAt r.run.before r.pid = some (allocation,queued)) (position : Nat)
    (held : Aligned (Born history generation r.pid allocation)
      (pendingAt (.selected position) ledger) r.packets)
    (ordered : pendingPair (.selected position) (.staged generation r.pid allocation) ledger =
      pendingAt (.selected position) ledger ++ pendingAt (.staged generation r.pid allocation) ledger) :
    let source := Pending.selected position
    let target := Pending.staged generation r.pid allocation
    let after := transferLocation source target ledger
    Step ledger after ∧ Valid births after ∧ QueueInv history after r.run.after ∧
      pendingAt source after = [] ∧
      pendingAt target after = pendingAt source ledger ++ pendingAt target ledger ∧
      (∀ ticket ∈ pendingAt source ledger, (ticket,Status.pending target) ∈ after) ∧
      (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after) := by
  dsimp only
  let source := Pending.selected position
  let target := Pending.staged generation r.pid allocation
  let after := transferLocation source target ledger
  obtain ⟨_,stamp,packets,_,sameEpoch,stagedBefore,stagedAfter,others⟩ := restore_receipt_views r run
  have fields : stamp = allocation ∧ packets = queued :=
    Prod.mk.inj (Option.some.inj (stagedBefore.symm.trans resident))
  rw [fields.1,fields.2] at stagedAfter
  have step : Step ledger after := transferLocation_step source target ledger
  have aligned : Aligned (Born history generation r.pid allocation)
      (pendingAt target ledger) queued := by
    have related := before generation r.pid allocation
    simpa [stagedPackets,epoch,resident] using related
  have located : pendingAt target after = pendingAt source ledger ++ pendingAt target ledger := by
    rw [pendingAt_transfer_target]
    exact ordered
  refine ⟨step,step.valid valid,?_,pendingAt_transfer_source (by simp) ledger,
    located,?_,fun _ _ member => step.terminal member⟩
  · intro otherGeneration otherPid stamp
    by_cases same : Pending.staged otherGeneration otherPid stamp = target
    · obtain ⟨rfl,rfl,rfl⟩ := Pending.staged.inj same
      change Aligned _ (pendingAt target after) _
      rw [located]
      have restored : stagedPackets otherGeneration r.pid stamp r.run.after = r.packets ++ queued := by
        simp [stagedPackets,sameEpoch,epoch,stagedAfter]
      rw [restored]
      exact held.append aligned
    · rw [queue_replaced_other epoch sameEpoch resident stagedAfter others same,
        pendingAt_transfer_other (by simp) same]
      exact before otherGeneration otherPid stamp
  · intro ticket member
    exact transferLocation_member member

/-- In the empty destination case used by the immediate no-key return, the
prepend order follows from the queue invariant itself. The held tickets and
peer-allocation match remain explicit entry obligations of this local cut. -/
theorem restore_empty_step (r : HandshakeSecurity.StagedConservation.Restore.Receipt)
    (run : r.Valid) (valid : Valid births ledger)
    (before : QueueInv history ledger r.run.before)
    (epoch : Packets.epoch r.run.before = some generation)
    (resident : stagedAt r.run.before r.pid = some (allocation,[])) (position : Nat)
    (held : Aligned (Born history generation r.pid allocation)
      (pendingAt (.selected position) ledger) r.packets) :
    let source := Pending.selected position
    let target := Pending.staged generation r.pid allocation
    let after := transferLocation source target ledger
    Step ledger after ∧ Valid births after ∧ QueueInv history after r.run.after ∧
      pendingAt source after = [] ∧ pendingAt target after = pendingAt source ledger := by
  have empty : pendingAt (.staged generation r.pid allocation) ledger = [] := by
    apply before.empty_pending
    simp [stagedPackets,epoch,resident]
  have ordered : pendingPair (.selected position) (.staged generation r.pid allocation) ledger =
      pendingAt (.selected position) ledger ++ pendingAt (.staged generation r.pid allocation) ledger := by
    rw [pendingPair_empty_right empty,empty,List.append_nil]
  have result := restore_step r run valid before epoch resident position held ordered
  exact ⟨result.1,result.2.1,result.2.2.1,result.2.2.2.1,
    by simpa only [empty,List.append_nil] using result.2.2.2.2.1⟩

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
