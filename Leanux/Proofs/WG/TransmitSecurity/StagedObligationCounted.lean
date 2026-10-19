import Leanux.Proofs.WG.TransmitSecurity.StagedObligationSettlement
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationDisposalFrames

/-! A native counted prefix disposal settles precisely the incoming tickets
at that queue. Other pending locations and every previous terminal stay intact.
These are local native transitions, not yet initialized Runner closure. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins
open AuthenticatedEffects.CausalJournal

theorem counted_step (p : HandshakeSecurity.StagedDisposal.Partition pid w v)
    (valid : Valid births ledger) (before : QueueInv history ledger w)
    (epoch : Packets.epoch w = some generation) (position : Nat)
    (arm : HandshakeSecurity.StagedDisposal.Arm) :
    let tickets := pendingAt (.staged generation pid p.stamp) ledger
    let selected := tickets.take p.removed
    let after := settle selected (.counted position arm) ledger
    Step ledger after ∧ Valid births after ∧ QueueInv history after v ∧
      selected.length = p.removed ∧
      (∀ ticket ∈ selected, (ticket,Status.terminal (.counted position arm)) ∈ after) ∧
      (∃ count, dropped w = some count ∧ dropped v = some (count+selected.length)) := by
  dsimp only
  let location := Pending.staged generation pid p.stamp
  let tickets := pendingAt location ledger
  let selected := tickets.take p.removed
  let after := settle selected (.counted position arm) ledger
  have unique : (keys ledger).Nodup := valid.1.symm ▸ valid.2
  have ticketUnique := pendingAt_unique unique location
  have aligned : Aligned (Born history generation pid p.stamp) tickets p.packets := by
    have aligned := before generation pid p.stamp
    rw [partition_before p epoch] at aligned
    exact aligned
  have selectedPending : ∀ ticket ∈ selected, ticket ∈ pendingAt location ledger := by
    intro ticket member
    exact List.mem_of_mem_take member
  have step : Step ledger after := settle_pending unique selectedPending
  have count : selected.length = p.removed :=
    (HandshakeSecurity.StagedConservation.native_partition p ticketUnique aligned).2.2.1
  refine ⟨step,step.valid valid,?_,count,?_,?_⟩
  · intro otherGeneration otherPid stamp
    by_cases same : Pending.staged otherGeneration otherPid stamp = location
    · have fields := Pending.staged.inj same
      obtain ⟨rfl,rfl,rfl⟩ := fields
      rw [partition_after p epoch,pendingAt_settle,filter_without_prefix ticketUnique]
      exact HandshakeSecurity.StagedConservation.aligned_drop aligned p.removed
    · rw [partition_other p epoch same,settle_other_location unique selectedPending same]
      exact before otherGeneration otherPid stamp
  · intro ticket member
    apply List.mem_map.mpr
    refine ⟨(ticket,Status.pending location),mem_pendingAt.mp (selectedPending ticket member),?_⟩
    simp only [ite_eq_left member]
  · change ∃ count, dropped w = some count ∧ dropped v = some (count+selected.length)
    simpa only [count] using p.charged

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
