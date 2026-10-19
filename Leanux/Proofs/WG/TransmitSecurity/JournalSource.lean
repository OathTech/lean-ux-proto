import Leanux.Proofs.WG.TransmitSecurity.DriverOuterProjection
import Leanux.Proofs.WG.HandshakeSecurity.ResponderDriverCuts
import Leanux.Proofs.WG.AuthenticatedEffects.TimerDispatchScope
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerObserved
import Leanux.Proofs.WG.TransmitSecurity.NativeAdapter
import Leanux.Proofs.WG.TransmitSecurity.WorkerEncryption
import Leanux.Proofs.WG.TransmitSecurity.CompletionReceipts
import Leanux.Proofs.WG.Queues.TxDisposition
import Leanux.Proofs.Logged.NativeCapture
import Leanux.Proofs.WG.AuthenticatedEffects.TransportDriverSource

/-! One retained journal for native reservation, packet allocation, encryption
ring selection, actual AEAD, queue publication and TX disposal. Hooks are placed
in the shared initialized driver, so their order is an execution order. -/
namespace Leanux.Proofs.WG.TransmitSecurity.Journal
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets

abbrev ResponderEvent := HandshakeSecurity.Responder.DriverCuts.Event

inductive Event where
  | rxOrigin (value : AuthenticatedEffects.TransportDriver.OriginEvent)
  | replay (value : AuthenticatedEffects.TransportDriver.Replay)
  | handshake (value : AuthenticatedEffects.HandshakeCausal.Event)
  | timerSelected (value : AuthenticatedEffects.TimerDispatch.Selection)
  | responder (value : ResponderEvent)
  | nonce (value : Nonce.Allocation)
  | reserved (slot : KeypairId) (run : WGRunWitness Nat)
  | allocated (packets : List DataPacket) (run : WGRunWitness (List SkbId))
  | routed (family addr : Nat) (packets : List Packet) (mtu : Nat) (run : WGRunWitness (Except Int PeerId))
  | ring (value : TxRing.Event)
  | polled (run : RunWitness (Option (List SkbId)))
  | encrypted (value : WorkerEncryption.Receipt)
  | encryptionReturn (item : Option (List SkbId)) (run : RunWitness Bool)
  | disposition (value : TxDisposition.Event)
  | socket (value : Completion.SocketReceipt)

def origin? : Event → Option AuthenticatedEffects.TransportDriver.OriginEvent
  | .rxOrigin value => some value
  | _ => none

def replay? : Event → Option AuthenticatedEffects.TransportDriver.Replay
  | .replay value => some value
  | _ => none

def handshake? : Event → Option AuthenticatedEffects.HandshakeCausal.Event
  | .handshake value => some value
  | _ => none

def responder? : Event → Option ResponderEvent | .responder value => some value | _ => none

def nonce? : Event → Option Nonce.Allocation | .nonce value => some value | _ => none

def encryption? : Event → Option WorkerEncryption.Receipt | .encrypted value => some value | _ => none

def disposition? : Event → Option TxDisposition.Event | .disposition value => some value | _ => none

def completion? : Event → Option Completion.Event
  | .disposition value => some (.disposition value)
  | .socket value => some (.socket value)
  | _ => none

def completionEvent : Completion.Event → Event
  | .disposition value => .disposition value
  | .socket value => .socket value

def ring? : Event → Option TxRing.Event
  | .ring value => some value
  | .disposition (.ring value) => some value
  | _ => none

def selection (pid : PeerId) : WGPrefix Event (Option (Peer × Option KeypairId)) :=
  focusStatePrefix Event.responder responder? (HandshakeSecurity.Responder.DriverCuts.selection pid)

def confirmation (pid : PeerId) (kid : KeypairId) : WGPrefix Event Bool :=
  focusStatePrefix Event.responder responder? (HandshakeSecurity.Responder.DriverCuts.confirmation pid kid)

def session (pid : PeerId) : WGPrefix Event Bool :=
  focusStatePrefix Event.responder responder? (HandshakeSecurity.Responder.DriverCuts.session pid)

def reserve (slot : KeypairId) : WGPrefix Event Nat :=
  receiptWGObserved (focusStatePrefix Event.nonce nonce? (Nonce.reserveObserved slot)) (.reserved slot)

def allocate (packets : List DataPacket) : WGPrefix Event (List SkbId) :=
  receiptWGObserved (liftWGPrefix (packets.mapM newTxSkb)) (.allocated packets)

def create (pid : PeerId) (item : List SkbId) : WGPrefix Event Unit :=
  NativeAdapter.lower (focusPrefix Event.disposition disposition? (TxDisposition.create pid item))

def front (family addr : Nat) (packets : List Packet) (mtu : Nat) : WGPrefix Event (Except Int PeerId) :=
  receiptWGObserved (liftWGPrefix (txFront family addr packets mtu)) (.routed family addr packets mtu)

def poll : PrefixM Event (Option (List SkbId)) :=
  receiptObserved (focusPrefix Event.ring ring? TxRing.poll) Event.polled

def encrypt (item : Option (List SkbId)) : PrefixM Event Bool :=
  receiptObserved (focusPrefix Event.encrypted encryption? (WorkerEncryption.tail item)) (.encryptionReturn item)

def transmit (pid : PeerId) : PrefixM Event Bool :=
  focusPrefix completionEvent completion? (Completion.step pid)

def hooks : Driver.Hooks Event where
  prepare := AuthenticatedEffects.TransportDriver.prepare Event.rxOrigin origin?
  counterCheck := AuthenticatedEffects.TransportDriver.counter Event.replay
  handshake := AuthenticatedEffects.HandshakeWorker.observed Event.handshake handshake?
  timerSelected := fun d j pid t we => AuthenticatedEffects.TimerDispatch.scope Event.timerSelected d j pid t we (pure 0)
  selection := selection
  confirmation := confirmation
  session := session
  reserve := reserve
  allocate := allocate
  create := create
  front := front
  poll := poll
  encrypt := encrypt
  transmit := transmit

def execute (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter Event Lean.Json :=
  Driver.executeObserved hooks trace placeholders

end Leanux.Proofs.WG.TransmitSecurity.Journal
