import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxRepaymentWorker
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedWorkerSendingPoints

/-! Original selected completion scope and ordered send-loop cuts. Source
points use actual prefix runs, independently of packet ownership accounts. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSending
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch HandshakeSecurity.StagedConservation

def body (pid : PeerId) (items : List SkbId) : PrefixM CausalJournal.Event Unit := do
  WorkerCompletion.prelude pid items
  let sent←sendLoop CausalJournal.completionOps pid items false
  finish CausalJournal.completionOps pid sent

theorem body_factor (pid : PeerId) (items : List SkbId) :
    CompletionEffects.completeWith CausalJournal.completionOps pid items=body pid items := by
  rw [←complete_factor]
  simp only [complete,body,WorkerCompletion.prelude,bind_assoc]

def scopedBody (pid : PeerId) (items : List SkbId) (h : List CausalJournal.Event) :
    PrefixM CausalJournal.Event Unit := do
  emitPrefix (WorkerCompletion.entered pid items h)
  body pid items
  emitPrefix (.scope (.exited h.length))

theorem scoped_run (pid : PeerId) (items : List SkbId) (w : World) (h : List CausalJournal.Event) :
    runPrefix (TxCleanup.completion pid items) w h=runPrefix (scopedBody pid items h) w h := by
  unfold TxCleanup.completion CompletionEffects.completeScoped
  rw [CausalScope.prefix_run,body_factor]
  simp only [scopedBody,runPrefix_bind,runPrefix_emit,WorkerCompletion.entered]
  cases performed : runPrefix (body pid items) w
      (h++[CausalJournal.Event.scope (.entered ⟨h.length,CausalSources.Cause.completion pid items⟩)]) with
  | mk result last=>
    cases result with
    | error stop=>rfl
    | ok pair=>obtain ⟨value,u⟩:=pair;cases value;rfl

theorem selected_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle)) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (do scopedBody pid items middle; CausalJournal.completionOps.dispose pid items head.keypair) u middle := by
  have inner:=scoped_run pid items u middle
  unfold TxCleanup.completion at inner
  rw [worker_selection_factor,runPrefix_bind,selected]
  change runPrefix (TxWorker.crypted pid items head) u middle=_
  rw [TxWorker.crypted,runPrefix_bind,runPrefix_bind,inner]

def tail (pid : PeerId) (items rest : List SkbId) (key : KeypairId) (position : Nat) (next : Bool) :
    PrefixM CausalJournal.Event Bool := do
  let sent←sendLoop CausalJournal.completionOps pid rest next
  finish CausalJournal.completionOps pid sent
  emitPrefix (.scope (.exited position))
  CausalJournal.completionOps.dispose pid items key

theorem loop_continuation
    (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
    (prepared : runPrefix (WorkerCompletion.prelude pid items) u
      (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last))
    (shape : items=done++rest)
    (iterations : runPrefix (sendLoop CausalJournal.completionOps pid done false) v last=(.ok (next,q),after)) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (tail pid items rest head.keypair middle.length next) q after := by
  have split : sendLoop CausalJournal.completionOps pid items false=
      (sendLoop CausalJournal.completionOps pid done false >>= fun next=>
        sendLoop CausalJournal.completionOps pid rest next) := by rw [shape,Sending.loop_append]
  rw [selected_continuation selected]
  simp only [scopedBody,body,bind_assoc,runPrefix_bind,runPrefix_emit,prepared,split,iterations,tail]

structure SendEntry (pid : PeerId) (w : World) (h : List CausalJournal.Event)
    (skb : SkbId) (packet : RunWitness DataPacket) (r : World) (events : List CausalJournal.Event) where
  items : List SkbId
  head : DataPacket
  selectedWorld : World
  selectedHistory : List CausalJournal.Event
  selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,selectedWorld),selectedHistory)
  loopWorld : World
  loopHistory : List CausalJournal.Event
  prepared : runPrefix (WorkerCompletion.prelude pid items) selectedWorld
    (selectedHistory++[WorkerCompletion.entered pid items selectedHistory])=(.ok ((),loopWorld),loopHistory)
  done : List SkbId
  rest : List SkbId
  shape : items=done++skb::rest
  next : Bool
  readWorld : World
  readHistory : List CausalJournal.Event
  iterations : runPrefix (sendLoop CausalJournal.completionOps pid done false) loopWorld loopHistory=
    (.ok (next,readWorld),readHistory)
  read : runPrefix (Sending.iterationPrefix skb) readWorld readHistory=(.ok (packet,r),events)

def SendEntry.afterSend (entry : SendEntry pid w h skb packet u middle) (sent : Bool) :
    PrefixM CausalJournal.Event Bool := do
  let next←Sending.afterSend packet entry.next sent
  tail pid entry.items entry.rest entry.head.keypair entry.selectedHistory.length next

theorem SendEntry.continuation (entry : SendEntry pid w h skb packet u middle) :
    runPrefix (CausalJournal.transmit pid) w h=
      runPrefix (CausalJournal.completionOps.send pid skb packet >>= entry.afterSend) u middle := by
  rw [loop_continuation entry.selected entry.prepared entry.shape entry.iterations]
  simp only [tail,sendLoop,Sending.iteration_factor,bind_assoc]
  rw [runPrefix_bind,entry.read]
  change runPrefix (Sending.afterPacket pid skb entry.next packet >>= fun next=>
    tail pid entry.items entry.rest entry.head.keypair entry.selectedHistory.length next) u middle=_
  simp only [Sending.afterPacket,bind_assoc]
  rfl

inductive Point (pid : PeerId) (w : World) (h : List CausalJournal.Event) :
    World → List CausalJournal.Event → Prop where
  | loopBoundary
      (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
      (prepared : runPrefix (WorkerCompletion.prelude pid items) u
        (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last))
      (shape : items=done++rest)
      (iterations : runPrefix (sendLoop CausalJournal.completionOps pid done false) v last=(.ok (next,q),after)) :
      Point pid w h q after
  | packetRead
      (selected : runPrefix (workerSelection pid) w h=(.ok (some ⟨items,head,true⟩,u),middle))
      (prepared : runPrefix (WorkerCompletion.prelude pid items) u
        (middle++[WorkerCompletion.entered pid items middle])=(.ok ((),v),last))
      (shape : items=done++skb::rest)
      (iterations : runPrefix (sendLoop CausalJournal.completionOps pid done false) v last=(.ok (next,q),after))
      (read : runPrefix (Sending.iterationPrefix skb) q after=(.ok (packet,r),events)) : Point pid w h r events

theorem Point.remaining (point : Point pid w h u middle) :
    ∃remaining,runPrefix (CausalJournal.transmit pid) w h=runPrefix remaining u middle := by
  cases point with
  | loopBoundary selected prepared shape iterations=>
    exact ⟨_,loop_continuation selected prepared shape iterations⟩
  | packetRead selected prepared shape iterations read=>
    rw [loop_continuation selected prepared shape iterations]
    simp only [tail,sendLoop,Sending.iteration_factor,bind_assoc]
    rw [runPrefix_bind,read]
    exact ⟨_,rfl⟩

noncomputable def remainder (point : Point pid w h u middle) : PrefixM CausalJournal.Event Bool :=
  Classical.choose point.remaining

theorem remainder_run (point : Point pid w h u middle) :
    runPrefix (CausalJournal.transmit pid) w h=runPrefix (remainder point) u middle :=
  Classical.choose_spec point.remaining

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSending
