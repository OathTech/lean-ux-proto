import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedConfigConcreteDispatch

/-! All declared dispatch-family contracts now come from fixed source
witnesses. Universal finer native-step coverage remains a distinct obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

variable {nativeConsume : Consume.Points.ChildPoints}
  {nativeNapi : Napi.Points.ChildPoints}
  {nativeWorker : Iteration.Points.ChildPoints}
  {nativeWork : WorkService.Points.ChildPoints}
  {nativeDispatch : Dispatch.Points.ChildPoints}
  {Good : History → World → Prop}

/-- Security: initialized runner cuts from every declared dispatch family
conserve packet lineage through actual configuration, traffic, lifecycle and
worker source paths. Finer native intervals and the final semantic evidence
interpretation remain explicit; this does not claim eventual completion. -/
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
    (acceptTx : ∀ledger pid h w,TxConcrete.Evidence ledger [] pid h w → Good h w) :
    Runner.Points.Covered
      (Service.RunnerCallbacks.runnerPoints (TrafficConcrete.servicePoints nativeConsume nativeNapi nativeWorker nativeWork)
        (Lifecycle.Concrete.dispatchPoints (DumpConcrete.dispatchPoints (XmitConcrete.dispatchPoints
          (TrafficConcrete.dispatchPoints (TrafficConcrete.servicePoints nativeConsume nativeNapi nativeWorker nativeWork)
            (TrafficConcrete.napiPoints nativeConsume nativeNapi) (dispatchPoints nativeDispatch))))))
      Good (Runner.Points.executeShape trace placeholders) [] :=
  TrafficConcrete.initialized (insideConsume:=nativeConsume) (insideNapi:=nativeNapi)
    (insideWorker:=nativeWorker) (insideWork:=nativeWork) (insideDispatch:=dispatchPoints nativeDispatch)
    trace placeholders carrierGood accountGood pendingGood acceptPeer acceptStaging acceptFront acceptEncryption acceptKeepalive acceptTx
    (configContract accountGood pendingGood acceptPeer acceptStaging acceptKeepalive)

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.ConfigConcrete
