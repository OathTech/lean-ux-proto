import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficConcretePoints

/-! Traffic source children share the concrete scheduler, worker and NAPI
instances. No receive/flood/batch callback proof is assumed by these joins. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def napiPoints (consume : Consume.Points.ChildPoints) (other : Napi.Points.ChildPoints) : Napi.Points.ChildPoints :=
  ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints consume)
    (IPv6.napiPoints (RoutedTransmit.napiPoints other))

def workerPoints (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  HandshakeConcrete.iterationPoints (TxConcrete.iterationPoints other)

def servicePoints (consume : Consume.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (worker : Iteration.Points.ChildPoints) (work : WorkService.Points.ChildPoints) : Service.Points.ChildPoints :=
  Service.ReceiveComposition.servicePoints consume (IPv6.napiPoints (RoutedTransmit.napiPoints napi))
    (workerPoints worker) (ProtocolSend.workPoints work)

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}
  {Good : History → World → Prop}

noncomputable def pollContracts
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w) :
    Napi.Points.ChildContracts (napiPoints nativeConsume nativeNapi) (napiPoints insideConsume insideNapi) Good :=
  ReceiveWorker.Composition.napiChildren accountGood acceptPeer
    (ReceiveWorker.Composition.stagedReceive acceptStaging
      (IPv6.receiveContracts accountGood (RoutedTransmit.transmitContract accountGood acceptStaging acceptPeer)))

noncomputable def serviceContracts
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (acceptTx : ∀ledger pid h w,TxConcrete.Evidence ledger [] pid h w → Good h w) :
    Service.Points.ChildContracts (servicePoints nativeConsume nativeNapi nativeWorker nativeWork)
      (servicePoints insideConsume insideNapi insideWorker insideWork) Good :=
  Service.Expanded.concreteChildren carrierGood accountGood pendingGood acceptPeer acceptKeepalive
    (Service.ReceiveComposition.schedulerChildren accountGood acceptPeer acceptStaging acceptEncryption
      (IPv6.receiveContracts accountGood (RoutedTransmit.transmitContract accountGood acceptStaging acceptPeer))
      {transmit:=TxConcrete.transmitContract acceptTx,
       handshake:=HandshakeConcrete.handshakeContract accountGood acceptPeer acceptKeepalive})
    (ProtocolSend.senderContract accountGood acceptPeer)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
