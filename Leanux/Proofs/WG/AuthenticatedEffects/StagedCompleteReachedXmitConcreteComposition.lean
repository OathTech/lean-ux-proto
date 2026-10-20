import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedXmitConcreteFrames

/-! Direct transmit dispatch uses its actual descriptor/fixture/routed source.
Configuration and the three receive/batch dispatch families remain separate. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.XmitConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def dispatchPoints (other : Dispatch.Points.ChildPoints) : Dispatch.Points.ChildPoints :=
  fun _ _ token w h u middle=>match token with
    | .family (.transmit family addr payload opts)=>Point ⟨family,addr,payload,opts⟩ w h u middle
    | token=>other _ _ token w h u middle

abbrev serviceDispatch (service : Service.Points.ChildPoints) (other : Dispatch.Points.ChildPoints) :=
  DumpConcrete.serviceDispatch service (dispatchPoints other)

structure DispatchOther (native inside : Service.Points.ChildPoints)
    (nativeOther insideOther : Dispatch.Points.ChildPoints) (Good : History → World → Prop) where
  config : ∀attrs,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.config attrs))
  receive : ∀family port message tos ll dest,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.receive family port message tos ll dest))
  flood : ∀count port family messages,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.flood count port family messages))
  batch : ∀items,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.batch items))

variable {native inside : Service.Points.ChildPoints}
  {nativeOther insideOther : Dispatch.Points.ChildPoints} {Good : History → World → Prop}

noncomputable def dispatchContracts
    (accountGood : ∀h w,Account h w → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (other : DispatchOther native inside nativeOther insideOther Good) :
    DumpConcrete.DispatchOther native inside (dispatchPoints nativeOther) (dispatchPoints insideOther) Good where
  config:=other.config
  receive:=other.receive
  flood:=other.flood
  batch:=other.batch
  transmit:=fun family addr payload opts=>{
    remainder:=fun _ _ _ _ point=>remainder (input:=⟨family,addr,payload,opts⟩) point
    continuation:=fun _ _ _ _ point=>remainder_run point
    coverage:=fun _ _ _ _ point=>point
    safe:=fun _ _ _ _ before point=>point.safe accountGood acceptStaging acceptPeer before}

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}

/-- Security: initialized direct transmit dispatch preserves the admitted
packet lineage through its fixed routed points, fixture scope and descriptor
repayment. Four dispatch bodies and finer native intervals remain boundaries. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (acceptTx : ∀ledger pid h w,TxConcrete.Evidence ledger [] pid h w → Good h w)
    (dispatch : DispatchOther
      (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints (RoutedTransmit.napiPoints nativeNapi))
        (HandshakeConcrete.iterationPoints (TxConcrete.iterationPoints nativeWorker)) (ProtocolSend.workPoints nativeWork))
      (Service.ReceiveComposition.servicePoints insideConsume (IPv6.napiPoints (RoutedTransmit.napiPoints insideNapi))
        (HandshakeConcrete.iterationPoints (TxConcrete.iterationPoints insideWorker)) (ProtocolSend.workPoints insideWork))
      nativeDispatch insideDispatch Good) :
    Runner.Points.Covered
      (Service.RunnerCallbacks.runnerPoints
        (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints (RoutedTransmit.napiPoints nativeNapi))
          (HandshakeConcrete.iterationPoints (TxConcrete.iterationPoints nativeWorker)) (ProtocolSend.workPoints nativeWork))
        (Lifecycle.Concrete.dispatchPoints (DumpConcrete.dispatchPoints (dispatchPoints nativeDispatch))))
      Good (Runner.Points.executeShape trace placeholders) [] :=
  TxConcrete.initialized trace placeholders carrierGood accountGood pendingGood acceptPeer acceptStaging
    acceptEncryption acceptKeepalive acceptTx (dispatchContracts accountGood acceptStaging acceptPeer dispatch)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.XmitConcrete
