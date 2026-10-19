import Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmissionLedger
import Leanux.Proofs.WG.TransmitSecurity.StagedObligationTakeFrames

/-! Admission changes precisely the queue at the native peer allocation.
The ledger is not reconstructed from resident queues; all old terminal and
held/allocated records survive the append. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission
open Leanux Leanux.WG
open TransmitSecurity TransmitSecurity.Staged.Origins TransmitSecurity.Staged.Obligations
open CausalJournal

theorem queue_append (before : QueueInv history ledger w)
    (epoch : Packets.epoch w = some generation)
    (sameEpoch : Packets.epoch v = Packets.epoch w)
    (old : Staged.stagedAt w pid = some (stamp,packets))
    (after : Staged.stagedAt v pid = some (stamp,packets ++ added))
    (others : ∀ q, pid ≠ q → Staged.stagedAt v q = Staged.stagedAt w q)
    (born : Aligned (Born (history ++ [event]) generation pid stamp)
      (freshTickets history.length 0 added) added) :
    QueueInv (history ++ [event])
      (appendBirths ledger history.length (.staged generation pid stamp) added) v := by
  intro otherGeneration otherPid otherStamp
  by_cases same : Pending.staged generation pid stamp = .staged otherGeneration otherPid otherStamp
  · obtain ⟨rfl,rfl,rfl⟩ := Pending.staged.inj same
    rw [pending_append,ite_eq_left rfl]
    have aligned := before generation pid stamp
    have source : stagedPackets generation pid stamp w = packets := by
      simp [stagedPackets,epoch,old]
    have target : stagedPackets generation pid stamp v = packets ++ added := by
      simp [stagedPackets,sameEpoch,epoch,after]
    rw [source] at aligned
    rw [target]
    exact (aligned.history_append [event]).append born
  · rw [pending_other same]
    rw [queue_replaced_other epoch sameEpoch old after others (Ne.symm same)]
    exact (before otherGeneration otherPid otherStamp).history_append [event]

theorem admission (validBefore : Valid births ledger) (bounded : Bounded history.length births)
    (before : QueueInv history ledger w)
    (epoch : Packets.epoch w = some generation)
    (sameEpoch : Packets.epoch v = Packets.epoch w)
    (old : Staged.stagedAt w pid = some (stamp,packets))
    (after : Staged.stagedAt v pid = some (stamp,packets ++ added))
    (others : ∀ q, pid ≠ q → Staged.stagedAt v q = Staged.stagedAt w q)
    (born : Aligned (Born (history ++ [event]) generation pid stamp)
      (freshTickets history.length 0 added) added) :
    let next := appendBirths ledger history.length (.staged generation pid stamp) added
    Valid (births ++ freshTickets history.length 0 added) next ∧
      Bounded (history ++ [event]).length (births ++ freshTickets history.length 0 added) ∧
      QueueInv (history ++ [event]) next v ∧
      (∀ ticket outcome, (ticket,Status.terminal outcome) ∈ ledger →
        (ticket,Status.terminal outcome) ∈ next) := by
  refine ⟨valid validBefore bounded,?_,queue_append before epoch sameEpoch old after others born,?_⟩
  · simpa only [List.length_append,List.length_singleton] using bounded_append bounded added
  · intro ticket outcome settled
    exact retains settled

end Leanux.Proofs.WG.AuthenticatedEffects.StagedAdmission
