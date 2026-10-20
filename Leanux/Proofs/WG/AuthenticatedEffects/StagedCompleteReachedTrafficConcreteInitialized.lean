import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedTrafficConcreteDispatch

/-! The original initialized runner now supplies receive, flood and batch
source contracts from the concrete shared worker graph. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

variable {nativeConsume insideConsume : Consume.Points.ChildPoints}
  {nativeNapi insideNapi : Napi.Points.ChildPoints}
  {nativeWorker insideWorker : Iteration.Points.ChildPoints}
  {nativeWork insideWork : WorkService.Points.ChildPoints}
  {Good : History → World → Prop}

/-- Security: initialized receive/flood/batch cuts conserve packet lineage
through their actual loops, worker sections, shared scheduling and routed
transmit. Configuration and deeper native-atom intervals remain explicit
coverage boundaries; no eventual-completion claim is made. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (carrierGood : ∀h w,CompleteProduct.Carrier h w → Good h w)
    (accountGood : ∀h w,Lifecycle.Points.Account h w → Good h w)
    (pendingGood : ∀h w,Timer.Points.Purge.Awaiting h w → Good h w)
    (acceptPeer : ∀ledger h w,PeerRetirement.Points.Evidence ledger [] [] h w.wg → Good h w)
    (acceptStaging : ∀ledger h w,StagingExpanded.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptFront : ∀ledger h w,FrontCuts.Evidence ledger [] [] h w.wg w.ambient → Good h w)
    (acceptEncryption : ∀ledger h w,EncryptionCallback.Evidence ledger [] [] h w → Good h w)
    (acceptKeepalive : ∀ledger pid (w : World) h (u : World) middle,
      KeepaliveExpanded.Evidence ledger [] [] pid w.wg w.ambient h middle u.wg u.ambient → Good middle u)
    (acceptTx : ∀ledger pid h w,TxConcrete.Evidence ledger [] pid h w → Good h w)
    (config : ∀attrs,Dispatch.Points.ChildSourceContract
      (serviceDispatch (servicePoints nativeConsume nativeNapi nativeWorker nativeWork)
        (napiPoints nativeConsume nativeNapi) nativeDispatch)
      (serviceDispatch (servicePoints insideConsume insideNapi insideWorker insideWork)
        (napiPoints insideConsume insideNapi) insideDispatch) Good (.family (.config attrs))) :
    Runner.Points.Covered
      (Service.RunnerCallbacks.runnerPoints (servicePoints nativeConsume nativeNapi nativeWorker nativeWork)
        (Lifecycle.Concrete.dispatchPoints (DumpConcrete.dispatchPoints (XmitConcrete.dispatchPoints
          (dispatchPoints (servicePoints nativeConsume nativeNapi nativeWorker nativeWork)
            (napiPoints nativeConsume nativeNapi) nativeDispatch)))))
      Good (Runner.Points.executeShape trace placeholders) [] :=
  XmitConcrete.initialized trace placeholders carrierGood accountGood pendingGood acceptPeer acceptStaging acceptFront
    acceptEncryption acceptKeepalive acceptTx
    (dispatchContracts accountGood acceptStaging acceptFront acceptPeer
      (serviceContracts carrierGood accountGood pendingGood acceptPeer acceptStaging acceptFront acceptEncryption acceptKeepalive acceptTx)
      (pollContracts accountGood acceptPeer acceptStaging acceptFront) config)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.TrafficConcrete
