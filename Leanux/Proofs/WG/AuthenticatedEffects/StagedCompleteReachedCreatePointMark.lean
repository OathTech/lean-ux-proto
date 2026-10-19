import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointEntries

/-! The uncrypted head mutation is reached from the original create read
and dead-peer guard. Its actual allocated ticket supplies the native cell;
no new unpublished allocation or post-error world is postulated. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CreateDisposal HandshakeSecurity.StagedDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
set_option maxHeartbeats 600000

def afterMark (pid : PeerId) : PrefixM CausalJournal.Event (Option Peer) := do
  let peer ← Admission.actualOps.access (getPeerMixed pid)
  if ← Admission.actualOps.step (branch .enqueuePeerQueueFull (peer.txQueue.count ≥ MAX_QUEUED_PACKETS)) then
    return none
  return some peer

def markedTail (pid : PeerId) (items : List SkbId) (first : SkbId) : PrefixM CausalJournal.Event Unit := do
  let ret ← do
    let some cached ← afterMark pid | pure (-WG.ENOSPC)
    queueInstall pid cached items
    queueAfter items
  let offered ← offered items ret
  offeredTail pid items first offered

theorem mark_residual (head : items.head?=some first)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory)) :
    runPrefix (body pid items) w history=
      runPrefix (do Admission.actualOps.access (setTxSkbPrefix first fun p=>{p with state:=.uncrypted})
                    markedTail pid items first) q readHistory := by
  rw [body,Admission.final_factor,head]
  simp only [Admission.actual,Admission.front,enqueue_factor,enqueue,queueBefore,head,
    bind_assoc,TxDisposition.bind_ite,pure_bind]
  simp only [runPrefix_bind,read,guarded,Bool.false_eq_true,ite_false]
  simp only [markedTail,afterMark,offeredTail,bind_assoc,TxDisposition.bind_ite,pure_bind,runPrefix_bind]

/-- Derive the real resident head from its original pending allocation at
this source-selected entry. The marked world retains that same ticket. -/
theorem uncrypted_cut (head : items.head?=some first)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (pending : PendingBatch history ledger items)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory)) :
    ∃ d packet, q.wg.dev=some d ∧ d.txSkbs[first]?=some packet ∧
      let cut:=markedWorld q d first packet .uncrypted
      Accounted (markedHistory q first readHistory) ledger debts (⟨.unpublished,pid,items⟩::locals) cut.wg ∧
      runPrefix (do let _ ← enter pid; markPrefix q first .uncrypted) w history=
        (.ok ((),cut),markedHistory q first readHistory) ∧
      runPrefix (body pid items) w history=
        runPrefix (do markDue q first; markedTail pid items first) cut (markedHistory q first readHistory) := by
  have account:=admission_queue_entry before read guarded
  obtain ⟨suffix,extended,_⟩:=QueueHandoff.focused_quiet (TxDisposition.nativeAccess (getPeerMixed pid)) w history
  change (runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history).2=_ at extended
  rw [read] at extended
  change readHistory=history++suffix at extended
  have batch : PendingBatch readHistory ledger items := by rw [extended]; exact pending.append suffix
  have member : first∈items := List.mem_of_mem_head? (by simp [head])
  obtain ⟨ticket,position,ordinal,generation,value,present,origin⟩:=batch first member
  have cell:=((account.entry.core.physical.resident ticket position ordinal present).at_origin origin).2
  obtain ⟨packet,resident,_⟩:=Option.map_eq_some_iff.mp cell
  cases device : q.wg.dev with
  | none=>simp [TxDisposition.txPackets,device] at resident
  | some d=>
    have found : d.txSkbs[first]?=some packet := by simpa [TxDisposition.txPackets,device] using resident
    obtain ⟨kept,residual,leading⟩:=mark_cut (state:=.uncrypted) device found account
    refine ⟨d,packet,rfl,found,kept,?_,?_⟩
    · rw [runPrefix_bind,enter_run read guarded]; exact leading
    · rw [mark_residual head read guarded,runPrefix_bind,runPrefix_bind,residual]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
