import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTxConcretePoints
import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedHandshakeComposition

/-! The initialized worker uses the fixed peer-transmit point family.
The evidence acceptance premise describes its packet account; it is not an
incoming callback correctness or arbitrary continuation certificate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

abbrev History := List Event

def iterationPoints (other : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  fun token w h u middle=>match token with
    | .transmit pid=>Point pid w h u middle
    | token=>other token w h u middle

noncomputable def transmitContract
    {nativeConsume insideConsume : Consume.Points.ChildPoints}
    {nativeNapi insideNapi : Napi.Points.ChildPoints}
    {nativeWorker insideWorker : Iteration.Points.ChildPoints} {Good : History → World → Prop}
    (accept : ∀ledger pid h w,Evidence ledger [] pid h w → Good h w) (pid : PeerId) :
    Iteration.Points.ChildSourceContract
      (ReceiveWorker.Composition.encryptionWorkerPoints nativeConsume nativeNapi
        (HandshakeConcrete.iterationPoints (iterationPoints nativeWorker)))
      (ReceiveWorker.Composition.encryptionWorkerPoints insideConsume insideNapi
        (HandshakeConcrete.iterationPoints (iterationPoints insideWorker))) Good (.transmit pid) where
  remainder:=fun _ _ _ _ point=>remainder point
  continuation:=fun _ _ _ _ point=>remainder_run point
  coverage:=fun _ _ _ _ point=>point
  safe:=by
    intro w h u middle before point
    obtain ⟨ledger,account⟩:=before.1
    exact accept ledger pid middle u (point.evidence account)

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}
  {Good : History → World → Prop}

/-- Security: initialized peer-transmit cuts conserve their original packet
lineage through native egress and repayment, with pending receipts explicit.
The fixed family is derived here; five dispatch bodies and deeper native
interval coverage remain named boundaries of the initialized theorem. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (acceptTx : ∀ledger pid h w,Evidence ledger [] pid h w → Good h w)
    (dispatch : DumpConcrete.DispatchOther
      (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints (RoutedTransmit.napiPoints nativeNapi))
        (HandshakeConcrete.iterationPoints (iterationPoints nativeWorker)) (ProtocolSend.workPoints nativeWork))
      (Service.ReceiveComposition.servicePoints insideConsume (IPv6.napiPoints (RoutedTransmit.napiPoints insideNapi))
        (HandshakeConcrete.iterationPoints (iterationPoints insideWorker)) (ProtocolSend.workPoints insideWork))
      nativeDispatch insideDispatch Good) :
    Runner.Points.Covered
      (Service.RunnerCallbacks.runnerPoints
        (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints (RoutedTransmit.napiPoints nativeNapi))
          (HandshakeConcrete.iterationPoints (iterationPoints nativeWorker)) (ProtocolSend.workPoints nativeWork))
        (Lifecycle.Concrete.dispatchPoints (DumpConcrete.dispatchPoints nativeDispatch))) Good (Runner.Points.executeShape trace placeholders) [] :=
  HandshakeConcrete.initialized trace placeholders carrierGood accountGood pendingGood acceptPeer acceptStaging
    acceptEncryption acceptKeepalive (transmitContract acceptTx) dispatch

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TxConcrete
