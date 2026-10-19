import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedCreatePointFrames

/-! Fixed native mutation prefixes and their actual remaining observer
emissions. Accounted is derived at the native post-write world, before those
quiet records; queue installation consumes exactly the unpublished alias. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation HandshakeSecurity.StagedDisposal CompleteCarrier StagedTerminalComplete Staged.Obligations
set_option maxHeartbeats 600000
variable {id : SkbId}

def accessEvent (event : LifetimeEvent) : CausalJournal.Event := CausalJournal.txEvent (.access event)

theorem access_run (action : MixedM α) (w : World) (history : List CausalJournal.Event)
    (result : Except Stop ((α×WGWorld)×Ambient)) (events : List LifetimeEvent)
    (native : ∀ h, runWGPrefix action w.wg w.ambient h=(result,h++events)) :
    runPrefix (Admission.actualOps.access action) w history=
      (result.map (fun ((value,g),a)=>(value,{w with wg:=g,ambient:=a})),history++events.map accessEvent) := by
  let out:=result.map (fun ((value,g),a)=>(value,{w with wg:=g,ambient:=a}))
  have lifted (h : List LifetimeEvent) : runPrefix (liftWGObserver action) w h=(out,h++events) := by
    rw [liftWGObserver_run,native]
  have inner (h : List TxDisposition.Event) :=
    focusPrefix_suffix TxDisposition.Event.access TxDisposition.accessEvent (liftWGObserver action)
      w h out events (lifted _)
  have outer:=focusPrefix_suffix CausalJournal.txEvent CausalJournal.txEvent?
    (TxDisposition.nativeAccess action) w history out (events.map TxDisposition.Event.access) (inner _)
  change runPrefix (focusPrefix CausalJournal.txEvent CausalJournal.txEvent?
    (TxDisposition.nativeAccess action)) w history = _
  rw [outer]
  simp only [List.map_map]
  rfl

theorem event_run (event : TxDisposition.Event) (w : World) (history : List CausalJournal.Event) :
    runPrefix (Admission.actualOps.event event) w history=(.ok ((),w),history++[CausalJournal.txEvent event]) := by
  exact focusPrefix_suffix CausalJournal.txEvent CausalJournal.txEvent? (emitPrefix event)
    w history (.ok ((),w)) [event] rfl

def markPrefix (entry : World) (id : SkbId) (state : PacketState) : PrefixM CausalJournal.Event Unit := do
  let packet ← liftPrefix (liftWG (getTxSkb id))
  emitPrefix (accessEvent (.packet (.read (.inl id) (packetStamp entry.wg id))))
  liftPrefix (liftWG (modifyDev fun d=>{d with txSkbs:=d.txSkbs.insert id {packet with state}}))

def markDue (entry : World) (id : SkbId) : PrefixM CausalJournal.Event Unit :=
  emitPrefix (accessEvent (.packet (.write (.inl id) (packetStamp entry.wg id))))

def markedHistory (entry : World) (id : SkbId) (history : List CausalJournal.Event) :=
  history++[accessEvent (.packet (.read (.inl id) (packetStamp entry.wg id)))]

def markedWorld (w : World) (d : Device) (id : SkbId) (packet : DataPacket) (state : PacketState) : World :=
  {w with wg:={w.wg with dev:=some {d with txSkbs:=d.txSkbs.insert id {packet with state}}}}

theorem mark_prefix_run (device : w.wg.dev=some d) (resident : d.txSkbs[id]?=some packet) :
    runPrefix (markPrefix w id state) w history=
      (.ok ((),markedWorld w d id packet state),markedHistory w id history) := by
  have read : (liftWG (getTxSkb id)).run w=.ok (packet,w) := by
    rw [liftWG_run,Packets.getTxSkb_run w.wg w.ambient d id packet device resident]
    rfl
  rw [markPrefix,runPrefix_bind,runPrefix_lift,read]
  simp only [runPrefix_bind,runPrefix_emit,runPrefix_lift]
  simp [liftWG_run,modifyDev,device,markedWorld,markedHistory,Except.map]

theorem mark_access_run (device : w.wg.dev=some d) (resident : d.txSkbs[id]?=some packet) :
    runPrefix (Admission.actualOps.access (setTxSkbPrefix id fun p=>{p with state})) w history=
      (.ok ((),markedWorld w d id packet state),markedHistory w id history++
        [accessEvent (.packet (.write (.inl id) (packetStamp w.wg id)))]) := by
  have native (h : List LifetimeEvent) :
      runWGPrefix (setTxSkbPrefix id fun p=>{p with state}) w.wg w.ambient h=
      (.ok (((),(markedWorld w d id packet state).wg),w.ambient),
        h++[.packet (.read (.inl id) (packetStamp w.wg id)),.packet (.write (.inl id) (packetStamp w.wg id))]) := by
    change runStatePrefix _ _ _ _=_
    rw [setTxSkbPrefix_run,Packets.getTxSkb_run w.wg w.ambient d id packet device resident,
      Packets.setTxSkb_run w.wg w.ambient d id packet (fun p=>{p with state}) device resident]
    simp only [Packets.update,device,Option.map_some,markedWorld]
  have result:=access_run _ w history _ _ native
  simpa only [Except.map,List.map_cons,List.map_nil,markedHistory,List.append_assoc,
    List.cons_append,List.nil_append,markedWorld] using result

theorem mark_cut (device : w.wg.dev=some d) (resident : d.txSkbs[id]?=some packet)
    (before : Accounted history ledger debts locals w.wg) :
    let v:=markedWorld w d id packet state
    Accounted (markedHistory w id history) ledger debts locals v.wg ∧
      runPrefix (Admission.actualOps.access (setTxSkbPrefix id fun p=>{p with state})) w history=
        runPrefix (markDue w id) v (markedHistory w id history) ∧
      runPrefix (markPrefix w id state) w history=(.ok ((),v),markedHistory w id history) := by
  dsimp only
  have native : ((setTxSkb id fun p=>{p with state}).run w.wg).run w.ambient=
      .ok (((),(markedWorld w d id packet state).wg),w.ambient) := by
    simpa only [Packets.update,device,Option.map_some,markedWorld] using
      Packets.setTxSkb_run w.wg w.ambient d id packet (fun p=>{p with state}) device resident
  have kept:=mark_accounted id state before native
  refine ⟨?_,?_,mark_prefix_run device resident⟩
  · exact disposition_history kept [.access (.packet (.read (.inl id) (packetStamp w.wg id)))]
  · rw [mark_access_run device resident]
    rfl

def queuePrefix (pid : PeerId) (peer : Peer) (items : List SkbId) : PrefixM CausalJournal.Event Unit :=
  liftPrefix (liftWG (setPeer pid {peer with txQueue:=peer.txQueue.enqueue items}))

def queueDue (pid : PeerId) (peer : Peer) (items : List SkbId) : PrefixM CausalJournal.Event Unit := do
  emitPrefix (accessEvent (.peer (.write pid peer.internalId)))
  Admission.actualOps.event (.queued pid items)

theorem queue_write_run (device : w.wg.dev=some d) :
    runPrefix (queueWrite pid peer items) w history=
      (.ok ((),{w with wg:=replacePeer w.wg d pid {peer with txQueue:=peer.txQueue.enqueue items}}),
        history++[accessEvent (.peer (.write pid peer.internalId))]) := by
  have native (h : List LifetimeEvent) :
      runWGPrefix (setPeerMixed pid {peer with txQueue:=peer.txQueue.enqueue items}) w.wg w.ambient h=
        (.ok (((),replacePeer w.wg d pid {peer with txQueue:=peer.txQueue.enqueue items}),w.ambient),
          h++[.peer (.write pid peer.internalId)]) := by
    change runStatePrefix _ _ _ _=_
    rw [setPeerMixed_run,install_native pid peer items device]
    simp only [device,Option.isSome_some,ite_true]
  exact access_run _ w history _ _ native

theorem queue_cut (device : w.wg.dev=some d) (resident : d.peers[pid]?=some peer)
    (before : Accounted history ledger debts (⟨.unpublished,pid,items⟩::locals) w.wg) :
    let v:={w with wg:=replacePeer w.wg d pid {peer with txQueue:=peer.txQueue.enqueue items}}
    Accounted history ledger debts locals v.wg ∧
      runPrefix (queuePrefix pid peer items) w history=(.ok ((),v),history) ∧
      runPrefix (queueInstall pid peer items) w history=runPrefix (queueDue pid peer items) v history := by
  dsimp only
  refine ⟨install_accounted pid peer items device resident before,?_,?_⟩
  · rw [queuePrefix,runPrefix_lift,liftWG_run,install_native pid peer items device]
    rfl
  · rw [queueInstall,runPrefix_bind,queue_write_run device]
    rw [queueDue,runPrefix_bind,runPrefix_emit]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.CreatePoints
