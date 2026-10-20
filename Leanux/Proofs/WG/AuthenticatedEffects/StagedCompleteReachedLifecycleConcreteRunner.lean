import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedLifecycleConcreteChildren

/-! Four lifecycle dispatch families now use concrete source contracts.
Eight other dispatch bodies retain their independent obligations; the original
runner, service graph and stronger deletion input are unchanged. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Concrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

abbrev dispatchPoints (other : Dispatch.Points.ChildPoints) : Dispatch.Points.ChildPoints :=
  Environment.joined points other

abbrev serviceDispatch (service : Service.Points.ChildPoints) (other : Dispatch.Points.ChildPoints) :=
  Service.Composition.dispatchPoints service (dispatchPoints other)

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
  dumpDevice : ∀ref,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.dumpDevice ref))
  dumpStart : ∀fd ref,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.dumpStart fd ref))
  dumpReceive : ∀fd,Dispatch.Points.ChildSourceContract (serviceDispatch native nativeOther)
    (serviceDispatch inside insideOther) Good (.family (.dumpReceive fd))

variable {native inside : Service.Points.ChildPoints}
  {nativeOther insideOther : Dispatch.Points.ChildPoints} {Good : History → World → Prop}

noncomputable def dispatchContracts
    (accountGood : ∀h w,Points.Account h w → Good h w)
    (contracts : Points.ChildContracts points points Good)
    (other : DispatchOther native inside nativeOther insideOther Good) :
    Service.Composition.DispatchOther native inside (dispatchPoints nativeOther) (dispatchPoints insideOther) Good where
  config:=other.config
  transmit:=other.transmit
  receive:=other.receive
  flood:=other.flood
  batch:=other.batch
  dumpDevice:=other.dumpDevice
  dumpStart:=other.dumpStart
  dumpReceive:=other.dumpReceive
  create:={
    remainder:=Environment.remainder .create contracts
    continuation:=fun _ _ _ _ point=>Environment.remainder_run .create contracts point
    coverage:=fun _ _ _ _ point=>point
    safe:=fun _ _ _ _ before point=>Environment.root_safe .create accountGood contracts before point}
  delete:={
    remainder:=Environment.remainder .delete contracts
    continuation:=fun _ _ _ _ point=>Environment.remainder_run .delete contracts point
    coverage:=fun _ _ _ _ point=>point
    safe:=fun _ _ _ _ before point=>Environment.root_safe .delete accountGood contracts before.1 point}
  openDevice:={
    remainder:=Environment.remainder .open contracts
    continuation:=fun _ _ _ _ point=>Environment.remainder_run .open contracts point
    coverage:=fun _ _ _ _ point=>point
    safe:=fun _ _ _ _ before point=>Environment.root_safe .open accountGood contracts before point}
  down:={
    remainder:=Environment.remainder .down contracts
    continuation:=fun _ _ _ _ point=>Environment.remainder_run .down contracts point
    coverage:=fun _ _ _ _ point=>point
    safe:=fun _ _ _ _ before point=>Environment.root_safe .down accountGood contracts before point}

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}

/-- Initialized create, delete, interface-up and interface-down source cuts
conserve packet lineage through concrete lifecycle callbacks. Deletion uses
its actual stronger entry and native quiescence check. Eight dispatch bodies,
three packet families and finer native interiors remain explicit boundaries. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (accountGood : ∀h w,Points.Account h w → Good h w)
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
        (dispatchPoints nativeDispatch)) Good (Runner.Points.executeShape trace placeholders) [] :=
  ProtocolSend.initialized trace placeholders carrierGood accountGood pendingGood acceptPeer acceptStaging
    acceptEncryption acceptKeepalive transmit workers
    (dispatchContracts accountGood (children accountGood pendingGood acceptPeer acceptStaging acceptKeepalive) dispatch)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.Lifecycle.Concrete
