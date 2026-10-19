import Leanux.Proofs.WG.RetirementSecurity.TxCoverageRunner


/-! The actual initialized runner supplies resident TX coverage with unique physical ownership at
every native syscall entry and returned world. Native callback contracts are
discharged; no incoming inventory or per-call coverage premise remains. -/
namespace Leanux.Proofs.WG.RetirementSecurity.TxCovered.Initialized
open Leanux Leanux.WG Leanux.Runner Leanux.Proofs.Logged
open TransmitSecurity RetirementSecurity Queues Queues.RxCredits Native
variable {id : SkbId}

theorem normal (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    TxCovered.Runner.Inv h w :=
  TxCovered.Runner.normal Syscalls.syscall_native trace placeholders run

theorem entries (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h)) :
    ∀index,index<trace.ops.size→TxCovered.Runner.OperationEntry trace placeholders index :=
  TxCovered.Runner.entries Syscalls.syscall_native trace placeholders run

/-- Executable acceptance supplies the same returned World and every original
operation entry, without an invariant or callback contract as input. -/
theorem accepted (trace : Trace) (placeholders : Bool)
    (run : Runner.executeTrace trace placeholders=.ok result) :
    ∃w h,runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h) ∧
      TxCovered.Runner.Inv h w ∧
      ∀index,index<trace.ops.size→TxCovered.Runner.OperationEntry trace placeholders index := by
  obtain ⟨w,h,_,source,_,_⟩ := RunnerAccount.accepted trace placeholders run
  exact ⟨w,h,source,normal trace placeholders source,entries trace placeholders source⟩

/-- Every resident TX cell at an empty-local boundary occurs once in one
actual peer queue. The queue's no-duplicate property counts packet positions,
while cross-peer separation rules out another logical owner. Ring aliases do
not add owners. -/
theorem unique_queue (before : TxCovered.Inv [] [] w)
    (resident : TxDisposition.txPackets w id=some packet) :
    ∃pid p,peerAt w pid=some p ∧ id∈txPeerItems p ∧ (txPeerItems p).Nodup ∧
      ∀other q,peerAt w other=some q→id∈txPeerItems q→other=pid := by
  have owners := before.2 id packet resident
  rcases owners with impossible | ⟨pid,queued⟩
  · simp [txLocalItems] at impossible
  · have nonempty : peerAt w pid ≠ none := by
      intro absent
      change id∈(((peerAt w pid).map (·.txQueue.all)).getD []).flatten at queued
      simp [absent] at queued
    obtain ⟨p,found⟩ := Option.ne_none_iff_exists'.mp nonempty
    have member : id∈txPeerItems p := by
      change id∈(((peerAt w pid).map (·.txQueue.all)).getD []).flatten at queued
      simpa [found,txPeerItems] using queued
    have inventory := before.1.2.1
    refine ⟨pid,p,found,member,inventory.queueUnique pid p found,?_⟩
    intro other q otherFound otherMember
    by_cases same : other=pid
    · exact same
    · exact False.elim (inventory.peersSeparate pid p other q found otherFound (Ne.symm same) id member otherMember)

/-- Initialized successful execution supplies the queue coverage and physical
uniqueness together, with no incoming invariant or callback premise. This is
an endpoint claim; terminal history and interrupted local continuations are
separate obligations. -/
theorem returned_unique (trace : Trace) (placeholders : Bool)
    (run : runPrefixOuter (RunnerAccount.observed trace placeholders) []=(.ok (result,w),h))
    (resident : TxDisposition.txPackets w.wg id=some packet) :
    ∃pid p,peerAt w.wg pid=some p ∧ id∈txPeerItems p ∧ (txPeerItems p).Nodup ∧
      ∀other q,peerAt w.wg other=some q→id∈txPeerItems q→other=pid :=
  unique_queue (normal trace placeholders run).2 resident

end Leanux.Proofs.WG.RetirementSecurity.TxCovered.Initialized
