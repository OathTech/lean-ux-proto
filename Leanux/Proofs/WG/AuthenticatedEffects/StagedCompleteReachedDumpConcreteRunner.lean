import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedDumpConcreteFrames

/-! Three dump dispatch bodies use their fixed original source witnesses.
Five dispatch bodies and three packet families remain independent obligations. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DumpConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

abbrev History := List Event

def dispatchPoints (other : Dispatch.Points.ChildPoints) : Dispatch.Points.ChildPoints :=
  fun _ _ token w h u middle=>match token with
    | .family (.dumpDevice ref) => RootPoint (.device ref) w h u middle
    | .family (.dumpStart fd ref) => RootPoint (.start fd ref) w h u middle
    | .family (.dumpReceive fd) => RootPoint (.receive fd) w h u middle
    | token => other _ _ token w h u middle

abbrev serviceDispatch (service : Service.Points.ChildPoints) (other : Dispatch.Points.ChildPoints) :=
  Lifecycle.Concrete.serviceDispatch service (dispatchPoints other)

structure DispatchOther (native inside : Service.Points.ChildPoints)
    (nativeOther insideOther : Dispatch.Points.ChildPoints) (Good : History → World → Prop) where
  config : ∀attrs,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.config attrs))
  transmit : ∀family addr payload opts,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.transmit family addr payload opts))
  receive : ∀family port message tos ll dest,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.receive family port message tos ll dest))
  flood : ∀count port family messages,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.flood count port family messages))
  batch : ∀items,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.batch items))

variable {native inside : Service.Points.ChildPoints}
  {nativeOther insideOther : Dispatch.Points.ChildPoints} {Good : History → World → Prop}

noncomputable def dispatchContracts
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (contracts : Lifecycle.Points.ChildContracts Lifecycle.Concrete.points Lifecycle.Concrete.points Good)
    (other : DispatchOther native inside nativeOther insideOther Good) :
    Lifecycle.Concrete.DispatchOther native inside (dispatchPoints nativeOther) (dispatchPoints insideOther) Good where
  config:=other.config
  transmit:=other.transmit
  receive:=other.receive
  flood:=other.flood
  batch:=other.batch
  dumpDevice:=fun ref=>{
    remainder:=remainder (.device ref) contracts
    continuation:=fun _ _ _ _ point=>remainder_run (.device ref) contracts point
    coverage:=fun _ _ _ _ point=>point
    safe:=fun _ _ _ _ before point=>root_safe (.device ref) accountGood contracts before.1 point}
  dumpStart:=fun fd ref=>{
    remainder:=remainder (.start fd ref) contracts
    continuation:=fun _ _ _ _ point=>remainder_run (.start fd ref) contracts point
    coverage:=fun _ _ _ _ point=>point
    safe:=fun _ _ _ _ before point=>root_safe (.start fd ref) accountGood contracts before.1 point}
  dumpReceive:=fun fd=>{
    remainder:=remainder (.receive fd) contracts
    continuation:=fun _ _ _ _ point=>remainder_run (.receive fd) contracts point
    coverage:=fun _ _ _ _ point=>point
    safe:=fun _ _ _ _ before point=>root_safe (.receive fd) accountGood contracts before.1 point}

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}

/-- Initialized dump source cuts conserve packet lineage through counted
cursor release and the original cancellation paths. Five dispatch bodies,
three packet families and finer native interiors remain explicit boundaries. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (transmit : ∀family addr packets mtu,Napi.Points.ChildSourceContract
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints nativeConsume) (IPv6.napiPoints nativeNapi))
      (ReceiveWorker.Composition.napiPoints (StagingExpanded.consumePoints insideConsume) (IPv6.napiPoints insideNapi))
      Good (.transmit family addr packets mtu))
    (workers : ReceiveWorker.Composition.EncryptionWorkerOther nativeConsume insideConsume
      (IPv6.napiPoints nativeNapi) (IPv6.napiPoints insideNapi) nativeWorker insideWorker Good)
    (dispatch : DispatchOther
      (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints nativeNapi) nativeWorker (ProtocolSend.workPoints nativeWork))
      (Service.ReceiveComposition.servicePoints insideConsume (IPv6.napiPoints insideNapi) insideWorker (ProtocolSend.workPoints insideWork))
      nativeDispatch insideDispatch Good) :
    Runner.Points.Covered
      (Service.RunnerCallbacks.runnerPoints
        (Service.ReceiveComposition.servicePoints nativeConsume (IPv6.napiPoints nativeNapi) nativeWorker (ProtocolSend.workPoints nativeWork))
        (Lifecycle.Concrete.dispatchPoints (dispatchPoints nativeDispatch))) Good (Runner.Points.executeShape trace placeholders) [] :=
  Lifecycle.Concrete.initialized trace placeholders carrierGood accountGood pendingGood acceptPeer acceptStaging
    acceptEncryption acceptKeepalive transmit workers
    (dispatchContracts accountGood (Lifecycle.Concrete.children accountGood pendingGood acceptPeer acceptStaging acceptKeepalive) dispatch)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.DumpConcrete
