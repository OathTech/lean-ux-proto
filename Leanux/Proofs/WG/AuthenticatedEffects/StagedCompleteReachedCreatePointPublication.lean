import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointEntries

/-! The actual EPIPE branch reaches publication with queued ownership.
Its published-head prefix retains the borrowed owner and original scheduling,
repayment and create-tail continuation, on successful or stopped suffixes. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
set_option maxHeartbeats 600000

theorem enqueued_accounted
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (enqueued : runPrefix (Admission.actualOps.enqueue pid items) w history=(.ok (ret,v),middle))
    (accepted : ret=0 ∨ ret = -WG.EPIPE) : Accounted middle ledger debts locals v.wg := by
  have outcome:=Queue.enqueue_cases pid items before.entry
  have complete:=CompleteSource.focused_complete (TxDisposition.enqueue pid items) w before.complete
  change Complete (runPrefix (Admission.actualOps.enqueue pid items) w history).2 ledger at complete
  rw [enqueued] at outcome complete
  rcases outcome with ⟨code,_⟩ | ⟨_,entry⟩
  · rcases accepted with rfl | rfl <;> cases code
  · exact ⟨entry,complete⟩

theorem epipe_entry
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory))
    (enqueued : runPrefix (Admission.actualOps.enqueue pid items) q readHistory=(.ok (-WG.EPIPE,v),middle))
    (pipe : runPrefix (Admission.actualOps.step (branch .createDataEpipe true)) v middle=(.ok (true,s),middle)) :
    Accounted middle ledger debts locals s.wg := by
  have atQueue:=admission_queue_entry before read guarded
  have queued:=enqueued_accounted atQueue enqueued (Or.inr rfl)
  obtain ⟨cut,run,entry⟩:=CreateEntry.guard_entry .createDataEpipe true queued.entry
  have same:=run.symm.trans pipe
  simp only [Prod.mk.injEq,Except.ok.injEq] at same
  obtain ⟨⟨_,rfl⟩,_⟩:=same
  exact ⟨entry,queued.complete⟩

theorem epipe_residual (head : items.head?=some first)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory))
    (enqueued : runPrefix (Admission.actualOps.enqueue pid items) q readHistory=(.ok (-WG.EPIPE,v),middle))
    (pipe : runPrefix (Admission.actualOps.step (branch .createDataEpipe true)) v middle=(.ok (true,s),middle)) :
    runPrefix (body pid items) w history=
      runPrefix (do TxSource.publish Admission.actualOps items .dead
                    Admission.tail Admission.actualOps CreateDisposal.free pid items first (-WG.EPIPE)) s middle := by
  rw [body,Admission.final_factor,head]
  simp only [Admission.actual,Admission.front,bind_assoc,TxDisposition.bind_ite,pure_bind]
  simp only [runPrefix_bind,read,guarded,Bool.false_eq_true,ite_false,enqueued,
    show (-WG.EPIPE == -WG.EPIPE)=true from rfl,pipe,ite_true]

/-- The exact owner returned by the native borrow remains attached to the
head-state mutation. The release is the existing named child, not a quiet
or unrelated repayment inserted by this proof. -/
theorem epipe_published
    (head : items.head?=some first)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg)
    (read : runPrefix (Admission.actualOps.access (getPeerMixed pid)) w history=(.ok (peer,u),readHistory))
    (guarded : runPrefix (Admission.actualOps.step (branch .createDataDead peer.isDead)) u readHistory=
      (.ok (false,q),readHistory))
    (enqueued : runPrefix (Admission.actualOps.enqueue pid items) q readHistory=(.ok (-WG.EPIPE,v),middle))
    (pipe : runPrefix (Admission.actualOps.step (branch .createDataEpipe true)) v middle=(.ok (true,s),middle))
    (published : runPrefix (publishedPrefix items .dead) s middle=(.ok ((headId,owner),cut),recorded)) :
    PublishedPath ledger debts locals items .dead s middle headId owner cut recorded ∧
      runPrefix (body pid items) w history=
        runPrefix (do publicationSchedule owner
                      Admission.actualOps.release (some owner)
                      Admission.tail Admission.actualOps CreateDisposal.free pid items first (-WG.EPIPE)) cut recorded := by
  refine ⟨published_path (epipe_entry before read guarded enqueued pipe) published,?_⟩
  rw [epipe_residual head read guarded enqueued pipe,published_prefix_factor]
  simp only [bind_assoc,runPrefix_bind,published]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
