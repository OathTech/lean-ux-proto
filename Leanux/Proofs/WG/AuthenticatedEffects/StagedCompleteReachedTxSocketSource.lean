import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxSendingFrames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorCoverage

/-! Fixed socket front, native result and receipt cuts. Resumption retains
the original outer send witness as well as the inner socket witness. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocket
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity RetirementSecurity
open AllocatedObligation CompletionBatch CompletionFirstTerminal SocketInterior

def outer (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) (origin : World)
    (body : PrefixM CausalJournal.Event Bool) : PrefixM CausalJournal.Event Bool :=
  fun w=>ExceptT.mk fun h=>match runPrefix body w h with
    | (.error stop,last)=>(.error stop,last)
    | (.ok (value,v),last)=>(.ok (value,v),last++[.sendResult ⟨pid,skb,packet,⟨value,origin,v⟩⟩])

theorem outer_source (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (w : World) (h : List CausalJournal.Event) :
    runPrefix (CausalJournal.completionOps.send pid skb packet) w h=
      runPrefix (outer pid skb packet w (FirstTerminal.focused (Completion.send pid skb packet))) w h := by
  change runPrefix (receiptObserved (FirstTerminal.focused (Completion.send pid skb packet)) _) w h=_
  rw [runPrefix_receiptObserved]
  change _=(match runPrefix (FirstTerminal.focused (Completion.send pid skb packet)) w h with
    | (.error stop,last)=>(Except.error (α:=Bool×World) stop,last)
    | (.ok (value,v),last)=>(.ok (value,v),last++[CausalJournal.Event.sendResult ⟨pid,skb,packet,⟨value,w,v⟩⟩]))
  cases runPrefix (FirstTerminal.focused (Completion.send pid skb packet)) w h with
  | mk result last=>
    cases result with
    | error stop=>rfl
    | ok pair=>obtain ⟨value,v⟩:=pair;rfl

theorem socket_returned
    (front : runPrefix (socketFront pid packet peer ipv4) entry (h.filterMap CausalJournal.completion?)=
      (.ok (result,v),h.filterMap CausalJournal.completion?++events)) :
    runPrefix (FirstTerminal.focused (Completion.socket pid skb packet peer ipv4)) entry h=
      (.ok (resultCode result,resultWorld v result),h++events.map FirstTerminal.encode++
        [.old (.socket (receipt pid skb packet peer ipv4 entry result v))]) := by
  have native:=socket_cases pid skb packet peer ipv4 entry (h.filterMap CausalJournal.completion?)
  rw [front] at native
  have lifted:=focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ entry h
    (.ok (resultCode result,resultWorld v result))
    (events++[Completion.Event.socket (receipt pid skb packet peer ipv4 entry result v)])
    (by simpa only [List.append_assoc] using native)
  simpa only [FirstTerminal.focused,FirstTerminal.encode,Function.comp_apply,Journal.completionEvent,
    List.map_append,List.map_cons,List.map_nil,List.append_assoc] using lifted

theorem accounting_returned
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (h.filterMap CausalJournal.completion?)=(.ok (peer,u),h.filterMap CausalJournal.completion?++readEvents))
    (family : SelectedFamily ipv4 peer)
    (front : runPrefix (socketFront pid packet peer ipv4) (familyWorld ipv4 u)
      ((h++readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?)=
      (.ok (result,v),(h++readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?++events)) :
    runPrefix (Sending.accountingPrefix pid skb packet) w h=
      (.ok (resultCode result,resultWorld v result),
        (h++readEvents.map FirstTerminal.encode)++events.map FirstTerminal.encode++
          [.old (.socket (receipt pid skb packet peer ipv4 (familyWorld ipv4 u) result v))]) := by
  rw [Sending.prefix_family pid skb packet peer ipv4 w u h readEvents read family]
  exact socket_returned front

def afterReceipt (pid : PeerId) (packet : RunWitness DataPacket) (result : Except Int SentDatagram) :
    PrefixM CausalJournal.Event Bool := FirstTerminal.focused (afterSocket pid packet (resultCode result))

def receiptSuffix (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) (peer : RunWitness Peer)
    (ipv4 : Bool) (entry : World) (result : Except Int SentDatagram) (frontWorld : World) :
    PrefixM CausalJournal.Event Bool := do
  emitPrefix (.old (.socket (receipt pid skb packet peer ipv4 entry result frontWorld)))
  afterReceipt pid packet result

def resultStep (result : Except Int SentDatagram) : PrefixM CausalJournal.Event Int :=
  FirstTerminal.focused (resultPrefix result)

theorem resultStep_run (result : Except Int SentDatagram) (w : World) (h : List CausalJournal.Event) :
    runPrefix (resultStep result) w h=(.ok (resultCode result,resultWorld w result),h) := by
  have lifted:=focusPrefix_suffix FirstTerminal.encode CausalJournal.completion? _ w h
    (.ok (resultCode result,resultWorld w result)) []
    (by simpa only [List.append_nil] using result_total result w (h.filterMap CausalJournal.completion?))
  simpa only [resultStep,FirstTerminal.focused,List.map_nil,List.append_nil] using lifted

inductive Phase where
  | front
  | result
  | recorded

def cutWorld (phase : Phase) (v : World) (result : Except Int SentDatagram) : World :=
  match phase with | .front=>v | _=>resultWorld v result

def cutHistory (phase : Phase) (h : List CausalJournal.Event) (socket : Completion.SocketReceipt) :
    List CausalJournal.Event := match phase with | .recorded=>h++[.old (.socket socket)] | _=>h

def innerRemaining (phase : Phase) (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (entry : World) (result : Except Int SentDatagram) (v : World) :
    PrefixM CausalJournal.Event Bool := match phase with
  | .front=>do _←resultStep result;receiptSuffix pid skb packet peer ipv4 entry result v
  | .result=>receiptSuffix pid skb packet peer ipv4 entry result v
  | .recorded=>afterReceipt pid packet result

theorem innerRemaining_run (phase : Phase) (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (entry : World) (result : Except Int SentDatagram) (v : World)
    (h : List CausalJournal.Event) :
    runPrefix (innerRemaining phase pid skb packet peer ipv4 entry result v)
      (cutWorld phase v result) (cutHistory phase h (receipt pid skb packet peer ipv4 entry result v))=
      runPrefix (afterReceipt pid packet result) (resultWorld v result)
        (h++[.old (.socket (receipt pid skb packet peer ipv4 entry result v))]) := by
  cases phase <;> simp only [innerRemaining,cutWorld,cutHistory,receiptSuffix,runPrefix_bind,resultStep_run,runPrefix_emit]

theorem continuation
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (h.filterMap CausalJournal.completion?)=(.ok (peer,u),h.filterMap CausalJournal.completion?++readEvents))
    (family : SelectedFamily ipv4 peer)
    (front : runPrefix (socketFront pid packet peer ipv4) (familyWorld ipv4 u)
      ((h++readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?)=
      (.ok (result,v),(h++readEvents.map FirstTerminal.encode).filterMap CausalJournal.completion?++events))
    (phase : Phase) :
    runPrefix (CausalJournal.completionOps.send pid skb packet) w h=
      runPrefix (outer pid skb packet w (innerRemaining phase pid skb packet peer ipv4 (familyWorld ipv4 u) result v))
        (cutWorld phase v result)
        (cutHistory phase ((h++readEvents.map FirstTerminal.encode)++events.map FirstTerminal.encode)
          (receipt pid skb packet peer ipv4 (familyWorld ipv4 u) result v)) := by
  have inner : runPrefix (FirstTerminal.focused (Completion.send pid skb packet)) w h=
      runPrefix (afterReceipt pid packet result) (resultWorld v result)
        (((h++readEvents.map FirstTerminal.encode)++events.map FirstTerminal.encode)++
          [.old (.socket (receipt pid skb packet peer ipv4 (familyWorld ipv4 u) result v))]) := by
    rw [Sending.focused_factor,runPrefix_bind,accounting_returned read family front]
    rfl
  rw [outer_source]
  change (match runPrefix (FirstTerminal.focused (Completion.send pid skb packet)) w h with
    | (.error stop,last)=>(Except.error (α:=Bool×World) stop,last)
    | (.ok (value,q),last)=>(.ok (value,q),last++[CausalJournal.Event.sendResult ⟨pid,skb,packet,⟨value,w,q⟩⟩]))=_
  rw [inner]
  unfold outer
  change _=(match runPrefix (innerRemaining phase pid skb packet peer ipv4 (familyWorld ipv4 u) result v)
      (cutWorld phase v result) (cutHistory phase _ _) with
    | (.error stop,last)=>(Except.error (α:=Bool×World) stop,last)
    | (.ok (value,q),last)=>(.ok (value,q),last++[CausalJournal.Event.sendResult ⟨pid,skb,packet,⟨value,w,q⟩⟩]))
  rw [innerRemaining_run]

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxSocket
