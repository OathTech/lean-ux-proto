import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedRoutedTransmitFrames

/-! The receive scheduler's routed transmitter is supplied by its actual
caller source, including expanded staging and peer repayment. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def napiPoints (other : Napi.Points.ChildPoints) : Napi.Points.ChildPoints :=
  fun token w h u middle=>match token with
    | .transmit family addr packets mtu=>Point ⟨family,addr,packets,mtu⟩ w h u middle
    | token=>other token w h u middle

noncomputable def transmitContract
    {nativeConsume insideConsume : Consume.Points.ChildPoints}
    {nativeNapi insideNapi : Napi.Points.ChildPoints} {Good : History → World → Prop}
    (accountGood : ∀h w,Account h w → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (family addr : Nat) (packets : List Packet) (mtu : Nat) :
    Napi.Points.ChildSourceContract
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints nativeConsume) (IPv6.napiPoints (napiPoints nativeNapi)))
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints insideConsume) (IPv6.napiPoints (napiPoints insideNapi)))
      Good (.transmit family addr packets mtu) where
  remainder:=fun _ _ _ _ point=>remainder point
  continuation:=fun _ _ _ _ point=>remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=fun _ _ _ _ before point=>point.safe accountGood acceptStaging acceptPeer before

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}
  {Good : History → World → Prop}

/-- Initialized routed transmit conserves packet lineage through its actual
front return, expanded staging and counted repayment. The front's internal
intervals, two packet families and five dispatch bodies remain boundaries. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (workers : ReceiveWorker.Composition.EncryptionWorkerOther nativeConsume insideConsume
      (IPv6.napiPoints (napiPoints nativeNapi)) (IPv6.napiPoints (napiPoints insideNapi)) nativeWorker insideWorker Good)
    (dispatch : DumpConcrete.DispatchOther
      (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints (napiPoints nativeNapi)) nativeWorker (ProtocolSend.workPoints nativeWork))
      (Service.ReceiveComposition.servicePoints insideConsume (IPv6.napiPoints (napiPoints insideNapi)) insideWorker (ProtocolSend.workPoints insideWork))
      nativeDispatch insideDispatch Good) :
    Runner.Points.Covered
      (Service.RunnerCallbacks.runnerPoints
        (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints (napiPoints nativeNapi)) nativeWorker (ProtocolSend.workPoints nativeWork))
        (Lifecycle.Concrete.dispatchPoints (DumpConcrete.dispatchPoints nativeDispatch))) Good (Runner.Points.executeShape trace placeholders) [] :=
  DumpConcrete.initialized trace placeholders carrierGood accountGood pendingGood acceptPeer acceptStaging
    acceptEncryption acceptKeepalive (transmitContract accountGood acceptStaging acceptPeer) workers dispatch

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.RoutedTransmit
