import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedIPv6Frames
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedServiceReceiveComposition

/-! IPv6 receive is supplied by its actual child-free source. The runner
composition retains three packet contracts, the protocol sender and dispatch
bodies explicitly. Universal coverage of native interiors remains open. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.IPv6
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def napiPoints (other : Napi.Points.ChildPoints) : Napi.Points.ChildPoints :=
  fun token w h u middle=>match token with
    | .receive6 bytes=>Point bytes w h u middle
    | token=>other token w h u middle

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}
  {Good : History → World → Prop}

noncomputable def receiveContract
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (bytes : List UInt8) : Napi.Points.ChildSourceContract
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints nativeConsume) (napiPoints nativeNapi))
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints insideConsume) (napiPoints insideNapi))
      Good (.receive6 bytes) where
  remainder:=fun _ _ _ _ point=>IPv6.remainder point
  continuation:=fun _ _ _ _ point=>remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=fun _ _ _ _ before point=>carrierGood _ _ (point.carrier before)

noncomputable def receiveContracts
    (carrierGood : ∀h w,Napi.Points.Carrier h w → Good h w)
    (transmit : ∀family addr packets mtu,Napi.Points.ChildSourceContract
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints nativeConsume) (napiPoints nativeNapi))
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints insideConsume) (napiPoints insideNapi))
      Good (.transmit family addr packets mtu)) :
    ReceiveWorker.Composition.StagedReceiveOther nativeConsume insideConsume
      (napiPoints nativeNapi) (napiPoints insideNapi) Good where
  transmit:=transmit
  receive6:=receiveContract carrierGood

/-- Initialized runner source cuts conserve their packet lineage through
IPv6 receive without an assumed IPv6 callback contract. Routed transmit,
peer transmit, handshake, the flushed protocol sender and dispatch bodies
remain explicit premises, as does the boundary of declared native points. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (workGood : ∀h w,WorkService.Points.Carrier h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (transmit : ∀family addr packets mtu,Napi.Points.ChildSourceContract
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints nativeConsume) (napiPoints nativeNapi))
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints insideConsume) (napiPoints insideNapi))
      Good (.transmit family addr packets mtu))
    (workers : ReceiveWorker.Composition.EncryptionWorkerOther nativeConsume insideConsume
      (napiPoints nativeNapi) (napiPoints insideNapi) nativeWorker insideWorker Good)
    (sender : ∀pid,WorkService.Points.ChildSourceContract
      (Service.Expanded.workPoints nativeWork) (Service.Expanded.workPoints insideWork) Good (.flushedSend pid))
    (dispatch : Service.Composition.DispatchOther
      (Service.ReceiveComposition.servicePoints nativeConsume (napiPoints nativeNapi) nativeWorker nativeWork)
      (Service.ReceiveComposition.servicePoints insideConsume (napiPoints insideNapi) insideWorker insideWork)
      nativeDispatch insideDispatch Good) :
    Runner.Points.Covered
      (Service.RunnerCallbacks.runnerPoints
        (Service.ReceiveComposition.servicePoints nativeConsume (napiPoints nativeNapi) nativeWorker nativeWork)
        nativeDispatch) Good (Runner.Points.executeShape trace placeholders) [] :=
  Service.ReceiveComposition.initialized trace placeholders carrierGood workGood pendingGood
    acceptPeer acceptStaging acceptEncryption acceptKeepalive (receiveContracts workGood transmit) workers sender dispatch

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.IPv6
