import Leanux.Proofs.WG.TransmitSecurity.StagedObligationQueueFrames
import Leanux.Proofs.WG.HandshakeSecurity.StagedDisposalFrames

/-! The exact queue views changed by a counted native prefix disposal. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
open Leanux Leanux.WG Staged.Origins

theorem partition_before (p : HandshakeSecurity.StagedDisposal.Partition pid w v)
    (epoch : Packets.epoch w = some generation) :
    stagedPackets generation pid p.stamp w = p.packets := by
  simp [stagedPackets,epoch,p.before]

theorem partition_after (p : HandshakeSecurity.StagedDisposal.Partition pid w v)
    (epoch : Packets.epoch w = some generation) :
    stagedPackets generation pid p.stamp v = p.packets.drop p.removed := by
  simp [stagedPackets,p.epoch,epoch,p.after]

theorem partition_other (p : HandshakeSecurity.StagedDisposal.Partition pid w v)
    (epoch : Packets.epoch w = some generation)
    (different : Pending.staged otherGeneration otherPid stamp ≠ .staged generation pid p.stamp) :
    stagedPackets otherGeneration otherPid stamp v = stagedPackets otherGeneration otherPid stamp w := by
  by_cases peer : pid = otherPid
  · subst otherPid
    by_cases time : generation = otherGeneration
    · subst otherGeneration
      have allocation : p.stamp ≠ stamp := by
        intro equal
        subst stamp
        exact different rfl
      simp [stagedPackets,p.epoch,epoch,p.before,p.after,allocation]
    · simp [stagedPackets,p.epoch,epoch,time]
  · simp only [stagedPackets,p.epoch,p.others otherPid peer]

theorem erased_other (epoch : Packets.epoch w = some generation)
    (sameEpoch : Packets.epoch v = Packets.epoch w)
    (before : stagedAt w pid = some (allocation,packets))
    (after : stagedAt v pid = none)
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

end Leanux.Proofs.WG.TransmitSecurity.Staged.Obligations
