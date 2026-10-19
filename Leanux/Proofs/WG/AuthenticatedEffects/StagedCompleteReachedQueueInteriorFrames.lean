import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueueInteriorSource

/-! Native queue reads leave packet ownership unchanged. A successful peek
changes only queue representation; the actual drop write transfers the exact
cached batch to the selected local before its observer emits removal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompleteCarrier
set_option maxHeartbeats 600000

theorem read_peer (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((getPeer pid).run w).run a=.ok ((p,w),a) := by
  simp [getPeer,getDev,device,resident]

theorem drop_read (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((dropRead pid).run w).run a=.ok (((p,p),w),a) := by
  simp [dropRead,getPeer,getDev,device,resident]

theorem drop_write (device : w.dev=some d) :
    ((dropWrite pid (p,p)).run w).run a=
      .ok (((),replacePeer w d pid {p with txQueue := p.txQueue.dropPeeked}),a) := by
  simp [dropWrite,setPeer,modifyDev,device,replacePeer]

theorem drop_run (device : w.dev=some d) (resident : d.peers[pid]?=some p) :
    ((txDropSource pid).run w).run a=
      .ok (((),replacePeer w d pid {p with txQueue := p.txQueue.dropPeeked}),a) := by
  rw [drop_continuation (drop_read device resident)]
  exact drop_write device

theorem peek_choice (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (chosen : ((p.txQueue.peek).run w).run a=.ok (((first,queue),v),b)) :
    ((peekChoice pid).run w).run a=.ok (((first,queue),v),b) := by
  unfold peekChoice
  simp only [StateT.run_bind,read_peer device resident]
  exact chosen

theorem peek_read (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (chosen : ((p.txQueue.peek).run w).run a=.ok (((first,queue),v),b)) :
    ((peekRead pid).run w).run a=.ok ((((first,queue),p),w),b) := by
  have same := (prev_peek_normal p.txQueue w v a b first queue chosen).2.2.2
  subst v
  rw [peekRead,MaterialOrigin.bind_ok_ambient]
  refine ⟨(first,queue),w,b,peek_choice device resident chosen,?_⟩
  rw [MaterialOrigin.bind_ok_ambient]
  exact ⟨p,w,b,read_peer device resident,rfl⟩

theorem peek_write (device : w.dev=some d) :
    ((peekWrite pid ((first,queue),p)).run w).run a=
      .ok (((),replacePeer w d pid {p with txQueue := queue}),a) := by
  simp [peekWrite,setPeer,modifyDev,device,replacePeer]

theorem peek_run (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (chosen : ((p.txQueue.peek).run w).run a=.ok (((first,queue),v),b)) :
    ((txPeekSource pid).run w).run a=
      .ok ((first,replacePeer w d pid {p with txQueue := queue}),b) := by
  rw [peek_continuation (peek_read device resident chosen)]
  simp only [peekTail,StateT.run_bind,peek_write device]
  rfl

/-- The same complete ledger is valid at the native peek setter, before any
write receipt. The cached batch retains its pending allocation occurrences. -/
theorem peek_accounted (before : Accounted history ledger [] locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (chosen : ((p.txQueue.peek).run w).run a=.ok (((first,queue),v),b)) :
    Accounted history ledger [] locals (replacePeer w d pid {p with txQueue := queue}) ∧
      (∀ items, first=some items → CreateDisposal.PendingBatch history ledger items) ∧
      queue.all=p.txQueue.all ∧ queue.peeked=first := by
  obtain ⟨entry,_,pending⟩ := TxSelection.peek_native pid a b before.entry
    (peek_run device resident chosen)
  have geometry := prev_peek_normal p.txQueue w v a b first queue chosen
  exact ⟨⟨entry,before.complete⟩,pending,geometry.2.1,geometry.2.2.1⟩

/-- At the dequeue setter, native queue ownership has already moved to the
same selected local. The ledger, its births and terminal receipts are unchanged. -/
theorem drop_accounted (a : Ambient) (before : Accounted history ledger [] locals w)
    (device : w.dev=some d) (resident : d.peers[pid]?=some p)
    (cached : p.txQueue.peeked=some items) :
    Accounted history ledger [] (⟨.selected,pid,items⟩::locals)
      (replacePeer w d pid {p with txQueue := p.txQueue.dropPeeked}) ∧
    CreateDisposal.PendingBatch history ledger items ∧
    p.txQueue.all=items::p.txQueue.dropPeeked.all := by
  have actualCached : ∀ q, peerAt w pid=some q → q.txQueue.peeked=some items := by
    intro q found
    have same : p=q := by simpa [peerAt,device,resident] using found
    simpa only [←same] using cached
  have entry := TxSelection.drop_native pid a a before.entry actualCached (drop_run device resident)
  exact ⟨⟨entry,before.complete⟩,DeadEntry.selected_pending entry,
    by simp [PrevQueue.all,PrevQueue.dropPeeked,cached]⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
