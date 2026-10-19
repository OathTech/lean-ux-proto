import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendCompletion
import Leanux.Proofs.WG.AuthenticatedEffects.RawAppendHandshake
import Leanux.Proofs.WG.AuthenticatedEffects.CookieConsumptionSource
import Leanux.Proofs.WG.TransmitSecurity.DriverSource

/-! Independent raw-append instantiation of the existing native Driver.
Only actual sending callbacks observe appends; all scheduling, native guards,
fixture operations and failed continuations are the same shared source spine.
The observer is not defined by filtering the final security journal. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity Queues Packets

def handshake (session : PeerId → WGPrefix Event Bool) (keepalive : PeerId → WGPrefix Event Unit) :
    WGPrefix Event Bool :=
  CookieConsumption.workerWith (fun msg => liftWGPrefix (cookieMessageConsume msg))
    (fun _ => receiveOps session keepalive)

def flushed (pid : PeerId) : WGPrefix Event Unit :=
  HandshakeSecurity.SendExchange.flushedWith liftWGPrefix
    (HandshakeSecurity.SendExchange.workerWith sendOps) pid

def hooks : Driver.Hooks Event where
  handshake := handshake
  flushedSend := flushed
  timerSelected := fun _ _ _ _ _ => pure 0
  selection := fun pid => liftWGPrefix (HandshakeSecurity.Responder.selectionPrefix pid)
  confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)
  session := fun pid => liftWGPrefix (beginSession pid)
  reserve := fun kid => liftWGPrefix (Nonce.reserveNative kid)
  allocate := fun packets => liftWGPrefix (packets.mapM newTxSkb)
  create := fun pid item => liftWGPrefix (createData pid item)
  front := fun family addr packets mtu => liftWGPrefix (txFront family addr packets mtu)
  poll := liftPrefix (liftWG TxRing.pollSource)
  encrypt := fun item => liftPrefix (RxWorkers.encryptStepTailSource item)
  transmit := completion

def execute (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter Event Lean.Json :=
  Driver.executeObserved hooks trace placeholders

end Leanux.Proofs.WG.AuthenticatedEffects.RawAppend
