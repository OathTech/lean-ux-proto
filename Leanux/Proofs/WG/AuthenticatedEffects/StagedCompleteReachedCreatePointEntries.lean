import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointMutation
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedAdmissionQueueFrames

/-! Actual read/guard and mark/full-queue prefixes of creation. Their entry
accounts are derived on the same source run; the queue write's pending
access/queued receipts retain the original create continuation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
set_option maxHeartbeats 600000

def enter (pid : PeerId) : PrefixM CausalJournal.Event Bool := do
  let peer ← Admission.actualOps.access (getPeerMixed pid)
  Admission.actualOps.step (branch .createDataDead peer.isDead)

def offeredTail (pid : PeerId) (items : List SkbId) (first : SkbId) (ret : Int) : PrefixM CausalJournal.Event Unit := do
  if ← Admission.actualOps.step (branch .createDataEpipe (ret == -WG.EPIPE)) then
    TxSource.publish Admission.actualOps items .dead
  Admission.tail Admission.actualOps CreateDisposal.free pid items first ret

def installedTail (pid : PeerId) (items : List SkbId) (first : SkbId) : PrefixM CausalJournal.Event Unit := do
  let ret ← queueAfter items
  let offered ← offered items ret
  offeredTail pid items first offered

def installPrefix (pid : PeerId) (items : List SkbId) : PrefixM CausalJournal.Event (Option Peer) := do
  if ← enter pid then return none
  queueBefore pid items

theorem enter_run
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory)) :
    runPrefix (enter pid) w history=(.ok (false,q),readHistory) := by
  simp only [enter,runPrefix_bind,read,guarded]

/-- A source-derived cached peer and full native account at the actual
pre-installation cut, without a successful enclosing create assumption. -/
theorem install_entry
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory))
    (prepared : runPrefix (queueBefore pid items) q readHistory=(.ok (some cached,v),middle)) :
    Accounted middle ledger debts (⟨.unpublished,pid,items⟩::locals) v.wg ∧
      (∃ d,v.wg.dev=some d ∧ d.peers[pid]?=some cached) ∧
      runPrefix (installPrefix pid items) w history=(.ok (some cached,v),middle) := by
  have entering:=admission_queue_entry before read guarded
  have focused : runPrefix (QueueHandoff.focused (QueueHandoff.before pid items)) q readHistory=
      (.ok (some cached,v),middle) := by rw [before_factor]; exact prepared
  obtain ⟨kept,resident⟩:=Queue.before_entry pid items entering.entry focused
  have complete:=CompleteSource.focused_complete (QueueHandoff.before pid items) q entering.complete
  rw [focused] at complete
  refine ⟨⟨kept,complete⟩,resident cached rfl,?_⟩
  rw [installPrefix,runPrefix_bind,enter_run read guarded]
  exact prepared

/-- The saved native queue write has the actual remaining branch/ring/tail,
including publication on EPIPE and the original refusal repayment. -/
theorem install_residual (head : items.head?=some first)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory))
    (prepared : runPrefix (queueBefore pid items) q readHistory=(.ok (some cached,v),middle)) :
    runPrefix (body pid items) w history=
      runPrefix (do queueInstall pid cached items; installedTail pid items first) v middle := by
  rw [body,Admission.final_factor,head]
  simp only [Admission.actual,Admission.front,enqueue_factor,enqueue,bind_assoc,
    TxDisposition.bind_ite,pure_bind]
  simp only [runPrefix_bind,read,guarded,Bool.false_eq_true,ite_false,prepared]
  simp only [installedTail,offeredTail,runPrefix_bind]
  cases written : runPrefix (queueInstall pid cached items) v middle with
  | mk outcome last=>cases outcome <;> rfl

/-- A literal native queue-prefix run and the exact original continuation at
its post-write/pre-receipt world. The unpublished alias is consumed only here. -/
theorem installed_native_cut (head : items.head?=some first)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory))
    (prepared : runPrefix (queueBefore pid items) q readHistory=(.ok (some cached,v),middle)) :
    ∃ d, v.wg.dev=some d ∧ d.peers[pid]?=some cached ∧
      let cut:={v with wg:=replacePeer v.wg d pid {cached with txQueue:=cached.txQueue.enqueue items}}
      Accounted middle ledger debts locals cut.wg ∧
      runPrefix (do let _ ← installPrefix pid items; queuePrefix pid cached items) w history=(.ok ((),cut),middle) ∧
      runPrefix (body pid items) w history=
        runPrefix (do queueDue pid cached items; installedTail pid items first) cut middle := by
  obtain ⟨atWrite,⟨d,device,resident⟩,leading⟩:=install_entry before read guarded prepared
  obtain ⟨account,native,residual⟩:=queue_cut device resident atWrite
  refine ⟨d,device,resident,account,?_,?_⟩
  · rw [runPrefix_bind,leading]; exact native
  · rw [install_residual head read guarded prepared,runPrefix_bind,runPrefix_bind,residual]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
