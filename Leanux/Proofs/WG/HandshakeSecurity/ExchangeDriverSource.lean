import Leanux.Proofs.WG.HandshakeSecurity.ExchangeObservation
import Leanux.Proofs.WG.HandshakeSecurity.SendExchangeErasure
import Leanux.Proofs.WG.TransmitSecurity.DriverSource

/-! The common driver records completed native exchange operations at their
actual callbacks. Its flushed-send callback covers scheduled and lifecycle drains;
all other native source choices and stopped prefixes remain in the shared spine. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriver
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets TransmitSecurity
open Origins.HandshakeSources

def receiveOps (session : PeerId → WGPrefix Exchange.Event Bool)
    (keepalive : PeerId → WGPrefix Exchange.Event Unit) : Ops (WGPrefix Exchange.Event) :=
  {AuthenticatedEffects.HandshakeWorker.ops session keepalive with
    create := Exchange.createResponse
    initiation := Exchange.consumeInitiation
    response := Exchange.consumeResponse}

def worker (session : PeerId → WGPrefix Exchange.Event Bool)
    (keepalive : PeerId → WGPrefix Exchange.Event Unit) : WGPrefix Exchange.Event Bool :=
  stepWith (receiveOps session keepalive)

def sendOps : SendExchange.Ops (WGPrefix Exchange.Event) where
  step := liftWGPrefix
  create := Exchange.createInitiation
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  initiated := fun pid => liftWGPrefix (timersHandshakeInitiated pid)
  put := fun peer => liftWGPrefix (peerPut peer)

def flushed (pid : PeerId) : WGPrefix Exchange.Event Unit :=
  SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith sendOps) pid

def hooks : Driver.Hooks Exchange.Event where
  timerSelected := fun _ _ _ _ _ => pure ()
  handshake := worker
  flushedSend := flushed
  selection := fun pid => liftWGPrefix (Responder.selectionPrefix pid)
  confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)
  session := Exchange.session
  reserve := fun kid => liftWGPrefix (Nonce.reserveNative kid)
  allocate := fun packets => liftWGPrefix (packets.mapM newTxSkb)
  create := fun pid item => liftWGPrefix (createData pid item)
  front := fun family addr packets mtu => liftWGPrefix (txFront family addr packets mtu)
  poll := liftPrefix (liftWG TxRing.pollSource)
  encrypt := fun item => liftPrefix (RxWorkers.encryptStepTailSource item)
  transmit := fun pid => liftPrefix (liftWG (txStep pid))

def execute (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter Exchange.Event Lean.Json :=
  Driver.executeObserved hooks trace placeholders

theorem sendOps_erases : SendExchange.Ops.Erases sendOps where
  step := fun _ => erasesStatePrefix_lift _
  create := Exchange.createInitiation_erases
  mac := fun _ _ => erasesStatePrefix_lift _
  traversal := fun _ => erasesStatePrefix_lift _
  sent := fun _ => erasesStatePrefix_lift _
  send := fun _ _ => erasesStatePrefix_lift _
  initiated := fun _ => erasesStatePrefix_lift _
  put := fun _ => erasesStatePrefix_lift _

theorem flushed_erases (pid : PeerId) : ErasesStatePrefix (flushed pid) (runFlushedSendWork pid) :=
  SendExchange.flushed_erases liftWGPrefix (fun _ => erasesStatePrefix_lift _)
    _ (SendExchange.worker_erases sendOps_erases) pid

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriver
