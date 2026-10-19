import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeTransfer
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeFrames

/-! A real take moves the exact incoming staged tickets to its caller-local
location before borrowing. These are local cut contracts; freshness of the
selected location must be supplied by the enclosing history carrier. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins
open AuthenticatedEffects.CausalJournal

theorem take_step (r : HandshakeSecurity.StagedConservation.Take.Receipt)
    (run : r.Valid) (p : Peer) (selected : r.run.value = some p)
    (valid : Valid births ledger) (before : QueueInv history ledger r.run.before)
    (epoch : Packets.epoch r.run.before = some generation) (position : Nat)
    (unused : pendingAt (.selected position) ledger = []) :
    let source := Pending.staged generation r.pid p.internalId
    let tickets := pendingAt source ledger
    let after := transferLocation source (.selected position) ledger
    Step ledger after ∧ Valid births after ∧ QueueInv history after r.run.after ∧
      pendingAt (.selected position) after = tickets ∧
      Aligned (Born history generation r.pid p.internalId) tickets p.staged ∧
      (∀ ticket ∈ tickets, (ticket,Status.pending (.selected position)) ∈ after) ∧
      (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ after) := by
  dsimp only
  let source := Pending.staged generation r.pid p.internalId
  let target := Pending.selected position
  let after := transferLocation source target ledger
  obtain ⟨_,_,sameEpoch,stagedBefore,stagedAfter,others⟩ := take_receipt_views r run p selected
  have step : Step ledger after := transferLocation_step source target ledger
  have aligned : Aligned (Born history generation r.pid p.internalId)
      (pendingAt source ledger) p.staged := by
    have related := before generation r.pid p.internalId
    simpa [stagedPackets,epoch,stagedBefore] using related
  refine ⟨step,step.valid valid,?_,pendingAt_transfer_unused unused,aligned,?_,fun _ _ member => step.terminal member⟩
  · intro otherGeneration otherPid stamp
    by_cases same : Pending.staged otherGeneration otherPid stamp = source
    · obtain ⟨rfl,rfl,rfl⟩ := Pending.staged.inj same
      change Aligned _ (pendingAt source after) _
      rw [pendingAt_transfer_source (by simp [source,target])]
      have empty : stagedPackets otherGeneration r.pid p.internalId r.run.after = [] := by
        simp [stagedPackets,sameEpoch,epoch,stagedAfter]
      rw [empty]
      exact .nil
    · rw [queue_replaced_other epoch sameEpoch stagedBefore stagedAfter others same,
        pendingAt_transfer_other same (by simp)]
      exact before otherGeneration otherPid stamp
  · intro ticket member
    exact transferLocation_member member

/-- The empty native take leaves the full ledger and projected queues intact. -/
theorem take_none_step (r : HandshakeSecurity.StagedConservation.Take.Receipt)
    (run : r.Valid) (empty : r.run.value = none)
    (before : QueueInv history ledger r.run.before) : QueueInv history ledger r.run.after := by
  have native : ((HandshakeSecurity.StagedConservation.Take.takePrefix r.pid).run r.run.before).run
      r.run.ambientBefore = .ok ((none,r.run.after),r.run.ambientAfter) := by
    rw [←empty]
    exact run
  obtain ⟨_,_,_,_,_,same,_⟩ := HandshakeSecurity.StagedConservation.Take.take_none
    r.pid r.run.before r.run.after r.run.ambientBefore r.run.ambientAfter native
  exact same ▸ before

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
