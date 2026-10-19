import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueueInteriorAccounts

/-! Original observed peek retains its queue-choice clock and two peer reads.
The native cached-queue setter precedes its write event, without changing
logical ownership or creating another packet occurrence. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompleteCarrier
set_option maxHeartbeats 600000

theorem completion_step (action : WG.M α) (w : World) (history : List CausalJournal.Event) :
    runPrefix (CausalJournal.completionOps.step action) w history=((liftWG action).run w,history) := by
  change runPrefix (focusPrefix FirstTerminal.encode CausalJournal.completion? (liftPrefix (liftWG action))) w history=_
  have focused := focusPrefix_suffix FirstTerminal.encode CausalJournal.completion?
    (liftPrefix (liftWG action)) w history ((liftWG action).run w) []
    (by simp only [runPrefix_lift,List.append_nil])
  simpa only [List.map_nil,List.append_nil] using focused

theorem completion_peer (pid : PeerId) : CausalJournal.completionOps.peer pid=access (getPeerMixed pid) := rfl

theorem modify_observed (f : Peer → Peer)
    (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (CausalJournal.completionOps.modifyPeer pid f) w history=
      (.ok ((),{w with wg:=replacePeer w.wg d pid (f p)}),history++[readEvent pid p,writeEvent pid (f p)]) := by
  have native : ((setPeer pid (f p)).run w.wg).run w.ambient=
      .ok (((),replacePeer w.wg d pid (f p)),w.ambient) := by
    simp [setPeer,modifyDev,device,replacePeer]
  change runPrefix (access (modifyPeerKeysPrefix pid f)) w history=_
  apply access_suffix (modifyPeerKeysPrefix pid f) w history
    (.ok (((),replacePeer w.wg d pid (f p)),w.ambient))
    [.peer (.read pid p.internalId),.peer (.write pid (f p).internalId)]
  intro h
  change runStatePrefix (modifyPeerKeysPrefix pid f) w.wg w.ambient h=_
  rw [modifyPeerKeysPrefix,runStatePrefix_bind,getPeerMixed_run,read_peer device resident]
  dsimp only
  rw [setPeerMixed_run,native,device]
  simp only [Option.isSome_some,ite_true,List.append_assoc,List.cons_append,List.nil_append]

/-- Literal observed peek, including its original queue-choice ambient result. -/
theorem peek_observed (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p)
    (chosen : ((p.txQueue.peek).run w.wg).run w.ambient=.ok (((first,queue),w.wg),b)) :
    runPrefix (TxSelection.peek pid) w history=
      (.ok (first,{w with wg:=replacePeer w.wg d pid {p with txQueue:=queue},ambient:=b}),
        history++[readEvent pid p,readEvent pid p,writeEvent pid p]) := by
  rw [TxSelection.peek,runPrefix_bind,completion_peer,access_read device resident]
  dsimp only
  rw [runPrefix_bind,completion_step,Leanux.Proofs.Framing.liftWG_run,chosen]
  dsimp only [Except.map]
  rw [runPrefix_bind,modify_observed (w:={w with ambient:=b}) (fun peer=>{peer with txQueue:=queue}) device resident]
  simp only [runPrefix_pure,List.append_assoc,List.cons_append,List.nil_append]
  rfl

def peekMutation (pid : PeerId) : PrefixM CausalJournal.Event (Option (List SkbId) × Peer) := do
  let peer ← access (getPeerMixed pid)
  let selected ← CausalJournal.completionOps.step peer.txQueue.peek
  let stored ← access (getPeerMixed pid)
  liftPrefix (liftWG (setPeer pid {stored with txQueue:=selected.2}))
  pure (selected.1,stored)

def peekDue (pid : PeerId) (read : Option (List SkbId) × Peer) : PrefixM CausalJournal.Event (Option (List SkbId)) := do
  emitPrefix (writeEvent pid read.2)
  pure read.1

theorem peek_mutation (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p)
    (chosen : ((p.txQueue.peek).run w.wg).run w.ambient=.ok (((first,queue),w.wg),b)) :
    runPrefix (peekMutation pid) w history=
      (.ok ((first,p),{w with wg:=replacePeer w.wg d pid {p with txQueue:=queue},ambient:=b}),
        history++[readEvent pid p,readEvent pid p]) := by
  rw [peekMutation,runPrefix_bind,access_read device resident]
  dsimp only
  rw [runPrefix_bind,completion_step,Leanux.Proofs.Framing.liftWG_run,chosen]
  dsimp only [Except.map]
  rw [runPrefix_bind,access_read (w:={w with ambient:=b}) device resident]
  dsimp only
  rw [runPrefix_bind,runPrefix_lift,Leanux.Proofs.Framing.liftWG_run]
  have setter : ((setPeer pid {p with txQueue:=queue}).run w.wg).run b=
      .ok (((),replacePeer w.wg d pid {p with txQueue:=queue}),b) := by
    simp [setPeer,modifyDev,device,replacePeer]
  rw [setter]
  simp only [Except.map,runPrefix_pure,List.append_assoc,List.cons_append,List.nil_append]

theorem peek_due (pid : PeerId) (first : Option (List SkbId)) (p : Peer) (w : World)
    (history : List CausalJournal.Event) :
    runPrefix (peekDue pid (first,p)) w history=(.ok (first,w),history++[writeEvent pid p]) := by
  rw [peekDue,runPrefix_bind,runPrefix_emit]
  rfl

/-- The original write event is the total remaining suffix after the cached
queue setter. Its source history is unchanged until that one event. -/
theorem peek_original_suffix (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p)
    (chosen : ((p.txQueue.peek).run w.wg).run w.ambient=.ok (((first,queue),w.wg),b)) :
    runPrefix (TxSelection.peek pid) w history=
      runPrefix (peekDue pid (first,p))
        {w with wg:=replacePeer w.wg d pid {p with txQueue:=queue},ambient:=b}
        (history++[readEvent pid p,readEvent pid p]) := by
  rw [peek_observed device resident chosen,peek_due]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

/-- The original cached cohort stays owned at the native setter with the
same ledger; no selected-local transfer occurs until the later dequeue. -/
theorem peek_pending (before : Accounted history ledger [] locals w.wg)
    (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p)
    (chosen : ((p.txQueue.peek).run w.wg).run w.ambient=.ok (((first,queue),w.wg),b)) :
    let after := replacePeer w.wg d pid {p with txQueue:=queue}
    let reads := history++[readEvent pid p,readEvent pid p]
    runPrefix (peekMutation pid) w history=(.ok ((first,p),{w with wg:=after,ambient:=b}),reads) ∧
      Accounted reads ledger [] locals after ∧
      (∀ items, first=some items → CreateDisposal.PendingBatch reads ledger items) ∧
      queue.all=p.txQueue.all ∧ queue.peeked=first ∧
      runPrefix (TxSelection.peek pid) w history=
        runPrefix (peekDue pid (first,p)) {w with wg:=after,ambient:=b} reads := by
  have readAccount := access_accounted before [.peer (.read pid p.internalId),.peer (.read pid p.internalId)]
  obtain ⟨account,pending,contents,cached⟩ := peek_accounted readAccount device resident chosen
  exact ⟨peek_mutation device resident chosen,account,pending,contents,cached,
    peek_original_suffix device resident chosen⟩

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
