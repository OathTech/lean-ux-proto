import Leanux.Proofs.WG.TransmitSecurity.CompletionAppendCut
import Leanux.Proofs.WG.HandshakeSecurity.StagedConservationSendResult

/-! The outer send result and the inner socket result are different source
cuts. In particular, the unsupported-family suffix returns false without
calling either socket; a socket receipt precedes any fallible byte accounting.
These local factors retain the original native choices and their order. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.CompletionFirstTerminal
open Leanux Leanux.WG Leanux.Proofs.Logged Leanux.Proofs.Framing Lifetimes Queues
open TransmitSecurity HandshakeSecurity.StagedConservation

def afterSocket (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) :
    PrefixM Completion.Event Bool := do
  let sent := ret == 0
  if ← liftPrefix (liftWG (branch .sendSkbOk sent)) then
    Completion.access (modifyPeerKeysPrefix pid fun p =>
      {p with txBytes := p.txBytes + packet.value.bytes.length})
  return sent

def afterPeer (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) : PrefixM Completion.Event Bool := do
  let family := (peer.value.endpoint.map (·.family)).getD 0
  let ret ← do
    if ← liftPrefix (liftWG (branch .sendSkbInet (family == AF_INET))) then
      Completion.socket pid skb packet peer true
    else if ← liftPrefix (liftWG (branch .sendSkbInet6 (family == AF_INET6))) then
      Completion.socket pid skb packet peer false
    else pure (-EAFNOSUPPORT)
  afterSocket pid packet ret

theorem send_factor (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket) :
    Completion.send pid skb packet =
      (captureObserved (Completion.access (getPeerMixed pid)) >>= afterPeer pid skb packet) := rfl

def refusedWorld (w : World) : World :=
  let first := CounterWindow.record w.ambient .sendSkbInet false
  let second := CounterWindow.record first .sendSkbInet6 false
  {w with ambient := CounterWindow.record second .sendSkbOk false}

private theorem branch_product (w : World) (decision : Decision) (value : Bool) :
    (liftWG (branch decision value)).run w =
      .ok (value,{w with ambient := CounterWindow.record w.ambient decision value}) := rfl

/-- The actual unsupported-family suffix returns false and emits no socket
receipt. It records exactly the three original negative branch decisions. -/
theorem unsupported (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w : World) (history : List Completion.Event)
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6) :
    runPrefix (afterPeer pid skb packet peer) w history =
      (.ok (false,refusedWorld w),history) := by
  simp only [afterPeer,beq_eq_false_iff_ne.mpr not4,beq_eq_false_iff_ne.mpr not6,
    runPrefix_bind,runPrefix_lift,branch_product,Bool.false_eq_true,ite_false]
  rfl

/-- The same native peer-read cut selects the unsupported-family suffix.
The returned history contains no extra inner socket event after that cut. -/
theorem send_unsupported (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (w u : World) (history middle : List Completion.Event)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w history =
      (.ok (peer,u),middle))
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6) :
    runPrefix (Completion.send pid skb packet) w history =
      (.ok (false,refusedWorld u),middle) := by
  rw [send_factor,runPrefix_bind,read]
  exact unsupported pid skb packet peer u middle not4 not6

theorem peer_read_socket_free (pid : PeerId) (w : World) (history : List Completion.Event) :
    (runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w history).2.filterMap
      Completion.socket? = history.filterMap Completion.socket? :=
  focusPrefix_other Completion.Event.disposition Completion.disposition? Completion.socket?
    (fun _ => rfl) (TxDisposition.nativeAccess (getPeerMixed pid)) w history

/-- The wrapper records the actual unsupported outer result after precisely
the observed peer-read prefix. Instantiating encode/decode to the final journal
uses its existing send callback; no second execution is introduced. -/
theorem unsupported_observed (encode : Completion.Event → E) (decode : E → Option Completion.Event)
    (record : SendResult.Receipt → E) (pid : PeerId) (skb : SkbId)
    (packet : RunWitness DataPacket) (peer : RunWitness Peer) (w u : World)
    (history : List E) (middle : List Completion.Event)
    (read : runPrefix (captureObserved (Completion.access (getPeerMixed pid))) w
      (history.filterMap decode) = (.ok (peer,u),history.filterMap decode ++ middle))
    (not4 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET)
    (not6 : (peer.value.endpoint.map (·.family)).getD 0 ≠ AF_INET6) :
    middle.filterMap Completion.socket? = [] ∧
    runPrefix (SendResult.observed record
      (focusPrefix encode decode (Completion.send pid skb packet)) pid skb packet) w history =
        (.ok (false,refusedWorld u),(history ++ middle.map encode) ++
          [record ⟨pid,skb,packet,⟨false,w,refusedWorld u⟩⟩]) := by
  have quiet := peer_read_socket_free pid w (history.filterMap decode)
  rw [read,List.filterMap_append] at quiet
  have empty : middle.filterMap Completion.socket? = [] := by
    apply List.eq_nil_of_length_eq_zero
    have lengths := congrArg List.length quiet
    simp only [List.length_append] at lengths
    omega
  refine ⟨empty,?_⟩
  apply SendResult.observed_completed
  exact focusPrefix_suffix encode decode _ w history _ middle
    (send_unsupported pid skb packet peer w u _ _ read not4 not6)

/-- A socket errno makes the outer send return false without another socket
attempt or packet mutation. Its already recorded inner receipt remains first. -/
theorem afterSocket_error (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int)
    (nonzero : ret ≠ 0) (w : World) (history : List Completion.Event) :
    runPrefix (afterSocket pid packet ret) w history =
      (.ok (false,{w with ambient := CounterWindow.record w.ambient .sendSkbOk false}),history) := by
  simp only [afterSocket,beq_eq_false_iff_ne.mpr nonzero,runPrefix_bind,runPrefix_lift,
    branch_product,Bool.false_eq_true,ite_false]
  rfl

def socketBody (pid : PeerId) (packet : RunWitness DataPacket) (peer : RunWitness Peer)
    (ipv4 : Bool) : PrefixM Completion.Event Int :=
  let endpoint := peer.value.endpoint.getD {family := 0,addr := 0,port := 0}
  if ipv4 then Completion.access (send4Prefix endpoint (some pid) packet.value.bytes packet.value.ds true)
  else Completion.access (send6Prefix endpoint (some pid) packet.value.bytes packet.value.ds true)

/-- Every completed inner call records its own result before accounting,
including errors which emit no datagram. This exact cut supplies the socket
terminal for the packet; outer failure and storage cleanup are later cuts. -/
theorem socket_result (pid : PeerId) (skb : SkbId) (packet : RunWitness DataPacket)
    (peer : RunWitness Peer) (ipv4 : Bool) (w v : World)
    (history middle : List Completion.Event) (ret : Int)
    (performed : runPrefix (socketBody pid packet peer ipv4) w history =
      (.ok (ret,v),middle)) :
    runPrefix (Completion.socket pid skb packet peer ipv4) w history =
      (.ok (ret,v),middle ++ [.socket ⟨pid,skb,packet,peer,ipv4,⟨ret,w,v⟩⟩]) := by
  change runPrefix (receiptObserved (socketBody pid packet peer ipv4) _) w history = _
  rw [runPrefix_receiptObserved,performed]

theorem afterSocket_appends (pid : PeerId) (packet : RunWitness DataPacket) (ret : Int) :
    Appends (afterSocket pid packet ret) := by
  unfold afterSocket
  apply Appends.bind (Appends.lift _)
  intro sent
  cases sent
  · exact Appends.pure _
  · exact Appends.bind (Appends.focus _ _ _) (fun _ => Appends.pure _)

/-- The actual appended datagram's inner receipt survives the complete native
send-accounting suffix, including a later Stop while updating peer counters.
The outer completed send receipt is therefore not another first terminal. -/
theorem append_before_accounting (pid : PeerId) (skb : SkbId)
    (packet : RunWitness DataPacket) (peer : RunWitness Peer) (ipv4 : Bool)
    (w : World) (u : WGWorld) (b : Ambient) (history : List Completion.Event)
    (datagram : SentDatagram)
    (front : (((Completion.socketArgs pid packet peer ipv4).beforeAppend).run w.wg).run w.ambient =
      .ok ((.ok datagram,u),b)) :
    let v := {w with wg := {u with sent := u.sent ++ [datagram]},ambient := b}
    ∃ middle suffix,
      (runPrefix (Completion.socket pid skb packet peer ipv4 >>= afterSocket pid packet) w history).2 =
        (history ++ middle) ++
          .socket ⟨pid,skb,packet,peer,ipv4,⟨0,w,v⟩⟩ :: suffix :=
  Completion.socket_append_retained pid skb packet peer ipv4 w u b history datagram front
    (afterSocket pid packet) (afterSocket_appends pid packet)

end Leanux.Proofs.WG.AuthenticatedEffects.CompletionFirstTerminal
