import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueueFrames
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationTakeFacts

/-! Exact native queue projections at the completed take cut, before borrow. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Leanux.Proofs.Logged Staged.Origins

/-- Replacing one queue at its existing allocation preserves every other
projected location, including all absent epoch/peer/allocation combinations. -/
theorem queue_replaced_other (epoch : Packets.epoch w = some generation)
    (sameEpoch : Packets.epoch v = Packets.epoch w)
    (before : stagedAt w pid = some (allocation,old))
    (after : stagedAt v pid = some (allocation,new))
    (others : ∀ q, pid ≠ q → stagedAt v q = stagedAt w q)
    (different : Pending.staged otherGeneration otherPid stamp ≠ .staged generation pid allocation) :
    stagedPackets otherGeneration otherPid stamp v = stagedPackets otherGeneration otherPid stamp w := by
  by_cases peer : pid = otherPid
  · subst otherPid
    by_cases time : generation = otherGeneration
    · subst otherGeneration
      have changed : allocation ≠ stamp := by
        intro equal
        subst stamp
        exact different rfl
      simp [stagedPackets,sameEpoch,epoch,before,after,changed]
    · simp [stagedPackets,sameEpoch,epoch,time]
  · simp only [stagedPackets,sameEpoch,others otherPid peer]

/-- A genuine completed take gives the entire resident batch and clears only
that allocation's queue; no completed key borrow is assumed. -/
theorem take_receipt_views (r : HandshakeSecurity.StagedConservation.Take.Receipt)
    (valid : r.Valid) (p : Peer) (selected : r.run.value = some p) :
    ∃ generation, Packets.epoch r.run.before = some generation ∧
      Packets.epoch r.run.after = Packets.epoch r.run.before ∧
      stagedAt r.run.before r.pid = some (p.internalId,p.staged) ∧
      stagedAt r.run.after r.pid = some (p.internalId,[]) ∧
      (∀ q, r.pid ≠ q → stagedAt r.run.after q = stagedAt r.run.before q) := by
  have run : ((HandshakeSecurity.StagedConservation.Take.takePrefix r.pid).run r.run.before).run
      r.run.ambientBefore = .ok ((some p,r.run.after),r.run.ambientAfter) := by
    rw [←selected]
    exact valid
  obtain ⟨d,device,resident,_,after,_⟩ := HandshakeSecurity.StagedConservation.Take.take_some
    r.pid r.run.before r.run.after r.run.ambientBefore r.run.ambientAfter p run
  refine ⟨d.ifindex,?_,?_,?_,?_,?_⟩
  · simp [Packets.epoch,device]
  · simp [Packets.epoch,device,after]
  · simp [stagedAt,device,resident]
  · simp [stagedAt,after]
  · intro q different
    simp [stagedAt,device,after,Std.TreeMap.getElem?_insert,different]

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
