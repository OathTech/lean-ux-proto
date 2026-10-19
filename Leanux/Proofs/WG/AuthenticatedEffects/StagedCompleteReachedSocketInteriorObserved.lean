import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedSocketInteriorSource

/-! Exact product-world socket points. The lifetime history is focused through
its original two wrappers; neither native erasure nor a new observer is used. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues TransmitSecurity
open CompletionFirstTerminal

def lifetimeHistory (history : List Completion.Event) : List LifetimeEvent :=
  (history.filterMap Completion.disposition?).filterMap TxDisposition.accessEvent

def lifetimeEvent (event : LifetimeEvent) : Completion.Event :=
  .disposition (.access event)

theorem access_run (a : MixedM α) (w : World) (history : List Completion.Event) :
    runPrefix (Completion.access a) w history =
      let out := runWGPrefix a w.wg w.ambient (lifetimeHistory history)
      (out.1.map (fun ((value,wg),ambient) => (value,{w with wg,ambient})),
        history ++ (out.2.drop (lifetimeHistory history).length).map lifetimeEvent) := by
  let out := runWGPrefix a w.wg w.ambient (lifetimeHistory history)
  change (out.1.map _,history ++
    (((history.filterMap Completion.disposition?) ++
      (out.2.drop (lifetimeHistory history).length).map TxDisposition.Event.access).drop
      (history.filterMap Completion.disposition?).length).map Completion.Event.disposition) = _
  simp only [List.drop_left,List.map_map]
  rfl

def endpoint (peer : RunWitness Peer) : Endpoint :=
  peer.value.endpoint.getD {family := 0,addr := 0,port := 0}

def socketFront (pid : PeerId) (packet : RunWitness DataPacket) (peer : RunWitness Peer)
    (ipv4 : Bool) : PrefixM Completion.Event (Except Int SentDatagram) :=
  Completion.access (beforeAppend (endpoint peer) (some pid) packet.value.bytes packet.value.ds true ipv4)

def resultWorld (w : World) (result : Except Int SentDatagram) : World :=
  {w with wg := appended w.wg result}

def receipt (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (entry : World)
    (result : Except Int SentDatagram) (frontWorld : World) : Completion.SocketReceipt :=
  ⟨pid,skb,packet,peer,ipv4,⟨resultCode result,entry,resultWorld frontWorld result⟩⟩

theorem body_cases (pid : PeerId) (packet : RunWitness DataPacket) (peer : RunWitness Peer)
    (ipv4 : Bool) (w : World) (history : List Completion.Event) :
    runPrefix (socketBody pid packet peer ipv4) w history =
      match runPrefix (socketFront pid packet peer ipv4) w history with
      | (.error stop,journal) => (.error stop,journal)
      | (.ok (result,u),journal) => (.ok (resultCode result,resultWorld u result),journal) := by
  have body : socketBody pid packet peer ipv4 = Completion.access
      (if ipv4 then send4Prefix (endpoint peer) (some pid) packet.value.bytes packet.value.ds true
       else send6Prefix (endpoint peer) (some pid) packet.value.bytes packet.value.ds true) := by
    cases ipv4 <;> rfl
  rw [body,access_run]
  change _ = match runPrefix (Completion.access _) w history with
    | (.error stop,journal) => (Except.error (α := Int × World) stop,journal)
    | (.ok (result,u),journal) => (.ok (resultCode result,resultWorld u result),journal)
  rw [access_run]
  simp only [runWGPrefix,runStatePrefix,StateT.run]
  rw [send_cases]
  cases runPrefix (beforeAppend (endpoint peer) (some pid) packet.value.bytes packet.value.ds true ipv4 w.wg)
      w.ambient (lifetimeHistory history) with
  | mk result journal => cases result with
    | error stop => rfl
    | ok value => rcases value with ⟨⟨result,u⟩,next⟩; rfl

/-- This is the original native sent-list append, followed by its result. -/
def resultPrefix : Except Int SentDatagram → PrefixM Completion.Event Int
  | .error code => pure code
  | .ok sent => do
    liftPrefix (liftWG (modify fun w => {w with sent := w.sent ++ [sent]}))
    pure 0

theorem result_total (result : Except Int SentDatagram) (w : World) (history : List Completion.Event) :
    runPrefix (resultPrefix result) w history =
      (.ok (resultCode result,resultWorld w result),history) := by
  cases result <;> rfl

theorem body_factor (pid : PeerId) (packet : RunWitness DataPacket) (peer : RunWitness Peer) (ipv4 : Bool) :
    socketBody pid packet peer ipv4 = (socketFront pid packet peer ipv4 >>= resultPrefix) := by
  funext w history
  change runPrefix (socketBody pid packet peer ipv4) w history =
    runPrefix (socketFront pid packet peer ipv4 >>= resultPrefix) w history
  rw [body_cases,runPrefix_bind]
  cases runPrefix (socketFront pid packet peer ipv4) w history with
  | mk out journal => cases out with
    | error stop => rfl
    | ok value => rcases value with ⟨result,u⟩; exact (result_total result u journal).symm

/-- A normal inner result emits its one receipt in the same returned world.
A Stop is precisely the failed original front and has no result world. -/
theorem socket_cases (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w : World) (history : List Completion.Event) :
    runPrefix (Completion.socket pid skb packet peer ipv4) w history =
      match runPrefix (socketFront pid packet peer ipv4) w history with
      | (.error stop,journal) => (.error stop,journal)
      | (.ok (result,u),journal) =>
        (.ok (resultCode result,resultWorld u result),journal ++ [.socket (receipt pid skb packet peer ipv4 w result u)]) := by
  change runPrefix (receiptObserved (socketBody pid packet peer ipv4) _) w history = _
  rw [runPrefix_receiptObserved,body_cases]
  cases runPrefix (socketFront pid packet peer ipv4) w history with
  | mk result journal => cases result with
    | error stop => rfl
    | ok value => rcases value with ⟨result,u⟩; rfl

/-- The native append changes precisely the sent list. No packet, queue,
peer or key store changes between the front and the result point. -/
theorem result_view (w : World) (result : Except Int SentDatagram) :
    StagedEntry.view (resultWorld w result).wg = StagedEntry.view w.wg := by
  cases result <;> rfl

theorem result_sent (w : World) (sent : SentDatagram) :
    (resultWorld w (.ok sent)).wg.sent = w.wg.sent ++ [sent] := rfl

theorem error_world (w : World) (code : Int) : resultWorld w (.error code) = w := rfl

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.SocketInterior
