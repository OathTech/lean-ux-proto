import Leanux.Proofs.WG.HandshakeSecurity.ExchangeDriverSource
import Leanux.Proofs.WG.AuthenticatedEffects.HandshakeWorkerParametric

/-! Completed exchange receipts decorate the existing shared callbacks. The
native consumer or creator runs once; its authenticated-effect observations
and internal Stop are retained. Session decoration belongs at the shared
session hook, not again inside each receiver callback. -/
namespace Leanux.Proofs.WG.HandshakeSecurity.ExchangeJoint
open Leanux Leanux.WG Leanux.Proofs.Logged Origins.HandshakeSources

def receiveOps (record : Exchange.Event → E) (base : Ops (WGPrefix E)) : Ops (WGPrefix E) :=
  {base with
    create := fun pid => receiptWGObserved (base.create pid) (record ∘ Exchange.Event.createResponse pid)
    initiation := fun msg => receiptWGObserved (base.initiation msg) (record ∘ Exchange.Event.consumeInitiation msg)
    response := fun msg => receiptWGObserved (base.response msg) (record ∘ Exchange.Event.consumeResponse msg)}

def sendOps (record : Exchange.Event → E) (base : SendExchange.Ops (WGPrefix E)) :
    SendExchange.Ops (WGPrefix E) :=
  {base with
    create := fun pid => receiptWGObserved (base.create pid) (record ∘ Exchange.Event.createInitiation pid)}

def nativeSendOps : SendExchange.Ops (WGPrefix E) where
  step := liftWGPrefix
  create := fun pid => liftWGPrefix (WG.createInitiation pid)
  mac := fun pid msg => liftWGPrefix (addMacToPacket pid msg)
  traversal := fun pid => liftWGPrefix (timersTraversal pid)
  sent := fun pid => liftWGPrefix (timersAnyAuthenticatedPacketSent pid)
  send := fun pid msg => liftWGPrefix (sendBufferToPeer pid msg)
  initiated := fun pid => liftWGPrefix (timersHandshakeInitiated pid)
  put := fun peer => liftWGPrefix (peerPut peer)

def flushed (record : Exchange.Event → E) (base : SendExchange.Ops (WGPrefix E))
    (pid : PeerId) : WGPrefix E Unit :=
  SendExchange.flushedWith liftWGPrefix (SendExchange.workerWith (sendOps record base)) pid

def session (record : Exchange.Event → E) (pid : PeerId) (body : WGPrefix E Bool) : WGPrefix E Bool :=
  receiptWGObserved body (record ∘ Exchange.Event.session pid)

end Leanux.Proofs.WG.HandshakeSecurity.ExchangeJoint
