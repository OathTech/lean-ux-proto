import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverSource

/-! A lawful entry format lets the same positivity proof certify legacy exchange
receipts or an extended cookie-consumer receipt without changing the T4 ledger. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.PeerReference
open Leanux Leanux.WG Leanux.Proofs.Logged Lifetimes Queues Packets TransmitSecurity
open Origins.HandshakeSources

structure CookieEntry where
  input : Key
  run : WGRunWitness Unit

class EntryFormat (E : Type) where
  before : E → WGWorld
  valid : E → Prop
  exchange : Exchange.Event → E
  exchange_before : ∀ e, before (exchange e) = e.before
  exchange_valid : ∀ e, e.Valid → valid (exchange e)
  cookie : Option (CookieEntry → E)
  cookie_before : ∀ record, cookie = some record → ∀ r, before (record r) = r.run.before
  cookie_valid : ∀ record, cookie = some record → ∀ r,
    r.run.Valid (cookieMessageConsume r.input) → valid (record r)

instance legacyEntryFormat : EntryFormat Exchange.Event where
  before := Exchange.Event.before
  valid := Exchange.Event.Valid
  exchange := id
  exchange_before := fun _ => rfl
  exchange_valid := fun _ h => h
  cookie := none
  cookie_before := by intro record impossible; cases impossible
  cookie_valid := by intro record impossible; cases impossible

namespace EntrySource
variable {E : Type} [EntryFormat E]

def createInitiation (pid : PeerId) : WGPrefix E (Option Key) :=
  receiptWGObserved (liftWGPrefix (WG.createInitiation pid))
    (fun r => EntryFormat.exchange (.createInitiation pid r))
def consumeInitiation (msg : Key) : WGPrefix E (Option PeerId) :=
  receiptWGObserved (liftWGPrefix (WG.consumeInitiation msg))
    (fun r => EntryFormat.exchange (.consumeInitiation msg r))
def createResponse (pid : PeerId) : WGPrefix E (Option Key) :=
  receiptWGObserved (liftWGPrefix (WG.createResponse pid))
    (fun r => EntryFormat.exchange (.createResponse pid r))
def consumeResponse (msg : Key) : WGPrefix E (Option PeerId) :=
  receiptWGObserved (liftWGPrefix (WG.consumeResponse msg))
    (fun r => EntryFormat.exchange (.consumeResponse msg r))
def session (pid : PeerId) : WGPrefix E Bool :=
  receiptWGObserved (liftWGPrefix (beginSession pid))
    (fun r => EntryFormat.exchange (.session pid r))
def cookie (msg : Key) : WGPrefix E Unit :=
  match EntryFormat.cookie (E := E) with
  | none => liftWGPrefix (cookieMessageConsume msg)
  | some record => receiptWGObserved (liftWGPrefix (cookieMessageConsume msg))
      (fun r => record ⟨msg,r⟩)

def receiveOps (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit) :
    Ops (WGPrefix E) :=
  {AuthenticatedEffects.HandshakeWorker.ops session keepalive with
    create := createResponse
    initiation := consumeInitiation
    response := consumeResponse
    cookieConsume := cookie}

def worker (session : PeerId → WGPrefix E Bool) (keepalive : PeerId → WGPrefix E Unit) : WGPrefix E Bool :=
  stepWith (receiveOps session keepalive)

def sendOps : SendExchange.Ops (WGPrefix E) where
  step := liftWGPrefix
  create := createInitiation
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  initiated := fun pid => liftWGPrefix (timersHandshakeInitiated pid)
  put := fun peer => liftWGPrefix (peerPut peer)

def flushed (pid : PeerId) : WGPrefix E Unit :=
  SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith sendOps) pid

def hooks : Driver.Hooks E where
  timerSelected := fun _ _ _ _ _ => pure 0
  handshake := worker
  flushedSend := flushed
  selection := fun pid => liftWGPrefix (Responder.selectionPrefix pid)
  confirmation := fun pid kid => liftWGPrefix (receivedWithKeypair pid kid)
  session := session
  reserve := fun kid => liftWGPrefix (Nonce.reserveNative kid)
  allocate := fun packets => liftWGPrefix (packets.mapM newTxSkb)
  create := fun pid item => liftWGPrefix (createData pid item)
  front := fun family addr packets mtu => liftWGPrefix (txFront family addr packets mtu)
  poll := liftPrefix (liftWG TxRing.pollSource)
  encrypt := fun item => liftPrefix (RxWorkers.encryptStepTailSource item)
  transmit := fun pid => liftPrefix (liftWG (txStep pid))

def execute (trace : Runner.Trace) (placeholders : Bool) : PrefixOuter E Lean.Json :=
  Driver.executeObserved hooks trace placeholders

theorem legacy_hooks : hooks (E := Exchange.Event) = ExchangeDriver.hooks := rfl

theorem legacy_execute (trace : Runner.Trace) (placeholders : Bool) :
    execute (E := Exchange.Event) trace placeholders = ExchangeDriver.execute trace placeholders := by
  unfold execute ExchangeDriver.execute
  rw [legacy_hooks]

end EntrySource
end Leanux.Proofs.WG.HandshakeSecurity.PeerReference
