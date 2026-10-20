import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedHandshakePoints

/-! The scheduler's handshake callback is the concrete canonical source;
its packet-changing callbacks have no incoming source-contract premise. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def iterationPoints (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  fun token w h u middle=>match token with
    | .handshake=>RootPoint w h u middle
    | token=>other token w h u middle

noncomputable def handshakeContract
    {nativeConsume insideConsume : Consume.Points.ChildPoints}
    {nativeNapi insideNapi : Napi.Points.ChildPoints}
    {nativeWorker insideWorker : Iteration.Points.ChildPoints} {Good : History → World → Prop}
    (accountGood : ∀h w,Carrier h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u) :
    Iteration.Points.ChildSourceContract
      (ReceiveWorker.Composition.encryptionWorkerPoints nativeConsume nativeNapi (iterationPoints nativeWorker))
      (ReceiveWorker.Composition.encryptionWorkerPoints insideConsume insideNapi (iterationPoints insideWorker)) Good .handshake where
  remainder:=fun _ _ _ _ point=>remainder point
  continuation:=fun _ _ _ _ point=>remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=fun _ _ _ _ before point=>root_safe accountGood acceptPeer acceptKeepalive before.1 point

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}
  {Good : History → World → Prop}

/-- Initialized handshake source cuts preserve the packet account through
scopes, receipts, timers, expanded keepalive and counted repayment. Peer
transmit, five dispatch bodies and finer native intervals remain boundaries. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (transmit : ∀pid,Iteration.Points.ChildSourceContract
      (ReceiveWorker.Composition.encryptionWorkerPoints nativeConsume
        (IPv6.napiPoints (RoutedTransmit.napiPoints nativeNapi)) (iterationPoints nativeWorker))
      (ReceiveWorker.Composition.encryptionWorkerPoints insideConsume
        (IPv6.napiPoints (RoutedTransmit.napiPoints insideNapi)) (iterationPoints insideWorker)) Good (.transmit pid))
    (dispatch : DumpConcrete.DispatchOther
      (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints (RoutedTransmit.napiPoints nativeNapi)) (iterationPoints nativeWorker) (ProtocolSend.workPoints nativeWork))
      (Service.ReceiveComposition.servicePoints insideConsume (IPv6.napiPoints (RoutedTransmit.napiPoints insideNapi)) (iterationPoints insideWorker) (ProtocolSend.workPoints insideWork))
      nativeDispatch insideDispatch Good) :
    Runner.Points.Covered
      (Service.RunnerCallbacks.runnerPoints
        (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints (RoutedTransmit.napiPoints nativeNapi)) (iterationPoints nativeWorker) (ProtocolSend.workPoints nativeWork))
        (Lifecycle.Concrete.dispatchPoints (DumpConcrete.dispatchPoints nativeDispatch))) Good (Runner.Points.executeShape trace placeholders) [] :=
  RoutedTransmit.initialized trace placeholders carrierGood accountGood pendingGood acceptPeer acceptStaging
    acceptEncryption acceptKeepalive
    { transmit:=transmit, handshake:=handshakeContract accountGood acceptPeer acceptKeepalive } dispatch

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.HandshakeConcrete
