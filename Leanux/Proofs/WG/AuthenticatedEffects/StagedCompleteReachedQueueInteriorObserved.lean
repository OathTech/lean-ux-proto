import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedQueueInteriorCoverage
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorObserved

/-! Existing queue access observations split at the native setter. These
calculations retain the original reads and exact lifetime suffix, including
the interval before the setter's write event and the later removal event. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompleteCarrier
set_option maxHeartbeats 600000

def access (a : MixedM α) : PrefixM CausalJournal.Event α :=
  focusPrefix FirstTerminal.encode CausalJournal.completion? (Completion.access a)

def queueAccessEvent (event : LifetimeEvent) : CausalJournal.Event :=
  .old (.disposition (.access event))

def readEvent (pid : PeerId) (p : Peer) := queueAccessEvent (.peer (.read pid p.internalId))
def writeEvent (pid : PeerId) (p : Peer) := queueAccessEvent (.peer (.write pid p.internalId))
def removedEvent (pid : PeerId) (items : List SkbId) : CausalJournal.Event :=
  .old (.disposition (.removed pid items))

theorem access_suffix (a : MixedM α) (w : World) (history : List CausalJournal.Event)
    (result : Except Stop ((α × WGWorld) × Ambient)) (events : List LifetimeEvent)
    (performed : ∀ h, runWGPrefix a w.wg w.ambient h=(result,h++events)) :
    runPrefix (access a) w history=
      (result.map (fun ((value,wg),ambient)=>(value,{w with wg,ambient})),
        history++events.map queueAccessEvent) := by
  have inner : runPrefix (Completion.access a) w (history.filterMap CausalJournal.completion?)=
      (result.map (fun ((value,wg),ambient)=>(value,{w with wg,ambient})),
        history.filterMap CausalJournal.completion? ++ events.map SocketInterior.lifetimeEvent) := by
    rw [SocketInterior.access_run,performed]
    simp only [List.drop_left]
  have encoded : FirstTerminal.encode ∘ SocketInterior.lifetimeEvent=queueAccessEvent := by
    funext event
    rfl
  simpa only [access,List.map_map,encoded] using focusPrefix_suffix FirstTerminal.encode
    CausalJournal.completion? (Completion.access a) w history _
    (events.map SocketInterior.lifetimeEvent) inner

theorem access_read (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (access (getPeerMixed pid)) w history=(.ok (p,w),history++[readEvent pid p]) := by
  have native := read_peer (a:=w.ambient) device resident
  have done := access_suffix (getPeerMixed pid) w history (.ok ((p,w.wg),w.ambient))
    [.peer (.read pid p.internalId)] (by intro h; exact (getPeerMixed_run pid w.wg w.ambient h).trans (by rw [native]))
  exact done

theorem access_write (device : w.wg.dev=some d) :
    runPrefix (access (setPeerMixed pid p)) w history=
      (.ok ((),{w with wg:=replacePeer w.wg d pid p}),history++[writeEvent pid p]) := by
  have native : ((setPeer pid p).run w.wg).run w.ambient=
      .ok (((),replacePeer w.wg d pid p),w.ambient) := by
    simp [setPeer,modifyDev,device,replacePeer]
  have done := access_suffix (setPeerMixed pid p) w history _ [.peer (.write pid p.internalId)] (by
    intro h
    change runStatePrefix (setPeerMixed pid p) _ _ _=_
    rw [setPeerMixed_run,native,device]
    rfl)
  exact done

def dropReads (pid : PeerId) : PrefixM CausalJournal.Event (Peer × Peer) := do
  let stored ← access (getPeerMixed pid)
  let queued ← access (getPeerMixed pid)
  pure (stored,queued)

def dropMutation (pid : PeerId) : PrefixM CausalJournal.Event (Peer × Peer) := do
  let read ← dropReads pid
  liftPrefix (liftWG (dropWrite pid read))
  pure read

def dropDue (pid : PeerId) (items : List SkbId) (read : Peer × Peer) : PrefixM CausalJournal.Event Unit := do
  emitPrefix (writeEvent pid read.1)
  emitPrefix (removedEvent pid items)

theorem drop_reads (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (dropReads pid) w history=
      (.ok ((p,p),w),history++[readEvent pid p,readEvent pid p]) := by
  simp only [dropReads,runPrefix_bind,access_read device resident,runPrefix_pure]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

theorem drop_mutation (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (dropMutation pid) w history=
      (.ok ((p,p),{w with wg:=replacePeer w.wg d pid {p with txQueue:=p.txQueue.dropPeeked}}),
        history++[readEvent pid p,readEvent pid p]) := by
  rw [dropMutation,runPrefix_bind,drop_reads device resident]
  dsimp only
  rw [runPrefix_bind,runPrefix_lift,Leanux.Proofs.Framing.liftWG_run,drop_write device]
  rfl

theorem drop_due (pid : PeerId) (items : List SkbId) (p q : Peer) (w : World)
    (history : List CausalJournal.Event) :
    runPrefix (dropDue pid items (p,q)) w history=
      (.ok ((),w),history++[writeEvent pid p,removedEvent pid items]) := by
  simp only [dropDue,runPrefix_bind,runPrefix_emit,List.append_assoc,List.cons_append,List.nil_append]

private theorem tx_access_suffix (a : MixedM α) (w : World) (history : List TxDisposition.Event)
    (result : Except Stop ((α × WGWorld) × Ambient)) (events : List LifetimeEvent)
    (performed : ∀ h, runWGPrefix a w.wg w.ambient h=(result,h++events)) :
    runPrefix (TxDisposition.nativeAccess a) w history=
      (result.map (fun ((value,wg),ambient)=>(value,{w with wg,ambient})),
        history++events.map TxDisposition.Event.access) := by
  apply focusPrefix_suffix TxDisposition.Event.access TxDisposition.accessEvent
  rw [liftWGObserver_run,performed]

private theorem tx_read (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (TxDisposition.nativeAccess (getPeerMixed pid)) w history=
      (.ok (p,w),history++[.access (.peer (.read pid p.internalId))]) := by
  refine tx_access_suffix (getPeerMixed pid) w history (.ok ((p,w.wg),w.ambient))
    [.peer (.read pid p.internalId)] ?_
  intro h
  change runStatePrefix (getPeerMixed pid) _ _ _=_
  rw [getPeerMixed_run,read_peer device resident]

private theorem tx_write (device : w.wg.dev=some d) :
    runPrefix (TxDisposition.nativeAccess (setPeerMixed pid p)) w history=
      (.ok ((),{w with wg:=replacePeer w.wg d pid p}),history++[.access (.peer (.write pid p.internalId))]) := by
  have native : ((setPeer pid p).run w.wg).run w.ambient=
      .ok (((),replacePeer w.wg d pid p),w.ambient) := by
    simp [setPeer,modifyDev,device,replacePeer]
  refine tx_access_suffix (setPeerMixed pid p) w history
    (.ok (((),replacePeer w.wg d pid p),w.ambient)) [.peer (.write pid p.internalId)] ?_
  intro h
  change runStatePrefix (setPeerMixed pid p) _ _ _=_
  rw [setPeerMixed_run,native,device]
  rfl

private theorem tx_drop (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (TxDisposition.drop pid items) w history=
      (.ok ((),{w with wg:=replacePeer w.wg d pid {p with txQueue:=p.txQueue.dropPeeked}}),
        history++[.access (.peer (.read pid p.internalId)),.access (.peer (.read pid p.internalId)),
          .access (.peer (.write pid p.internalId)),.removed pid items]) := by
  simp only [TxDisposition.drop,runPrefix_bind,tx_read device resident,tx_write device,runPrefix_emit]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

/-- The original journal emits two reads, then the setter's write, then its
one removal event. Its native mutation occurs between the reads and write. -/
theorem drop_observed (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (CausalJournal.completionOps.drop pid items) w history=
      (.ok ((),{w with wg:=replacePeer w.wg d pid {p with txQueue:=p.txQueue.dropPeeked}}),
        history++[readEvent pid p,readEvent pid p,writeEvent pid p,removedEvent pid items]) := by
  let events : List TxDisposition.Event := [.access (.peer (.read pid p.internalId)),
    .access (.peer (.read pid p.internalId)),.access (.peer (.write pid p.internalId)),.removed pid items]
  have inner := focusPrefix_suffix Completion.Event.disposition Completion.disposition?
    (TxDisposition.drop pid items) w (history.filterMap CausalJournal.completion?) _ events
    (tx_drop device resident)
  have outer := focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ w history _
    (events.map Completion.Event.disposition) inner
  exact outer

/-- The pending suffix belongs to the original invocation, and has no further
native failure site. It does not invent a second dequeue or terminal charge. -/
theorem drop_original_suffix (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (CausalJournal.completionOps.drop pid items) w history=
      runPrefix (dropDue pid items (p,p))
        {w with wg:=replacePeer w.wg d pid {p with txQueue:=p.txQueue.dropPeeked}}
        (history++[readEvent pid p,readEvent pid p]) := by
  rw [drop_observed device resident,drop_due]
  simp only [List.append_assoc,List.cons_append,List.nil_append]

theorem drop_source_split (device : w.wg.dev=some d) (resident : d.peers[pid]?=some p) :
    runPrefix (CausalJournal.completionOps.drop pid items) w history=
      runPrefix (dropMutation pid >>= dropDue pid items) w history := by
  rw [runPrefix_bind,drop_mutation device resident]
  exact drop_original_suffix device resident

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.QueueInterior
