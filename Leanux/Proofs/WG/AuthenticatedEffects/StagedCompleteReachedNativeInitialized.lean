import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeEvidence

/-! The initialized composition chooses a concrete accounting result. No
abstract safety predicate or semantic-acceptance hypothesis is supplied by
the caller; finer native source coverage remains a separate obligation. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

def children (consume : Consume.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (worker : Iteration.Points.ChildPoints) (work : WorkService.Points.ChildPoints)
    (dispatch : Dispatch.Points.ChildPoints) : Runner.Points.ChildPoints :=
  Service.RunnerCallbacks.runnerPoints (TrafficConcrete.servicePoints consume napi worker work)
    (Lifecycle.Concrete.dispatchPoints (DumpConcrete.dispatchPoints (XmitConcrete.dispatchPoints
      (TrafficConcrete.dispatchPoints (TrafficConcrete.servicePoints consume napi worker work)
        (TrafficConcrete.napiPoints consume napi) (ConfigConcrete.dispatchPoints dispatch)))))

/-- Security: every declared initialized source point carries its concrete
packet account or named selected, allocation or pending-receipt phase on the
actual WG projection, without an incoming accounting certificate. -/
theorem initialized (trace : Leanux.Runner.Trace) (placeholders : Bool) :
    Runner.Points.Covered (children nativeConsume nativeNapi nativeWorker nativeWork nativeDispatch)
      (fun h w=>Evidence h w.wg) (Runner.Points.executeShape trace placeholders) [] := by
  apply ConfigConcrete.initialized (Good:=fun h w=>Evidence h w.wg)
    (nativeConsume:=nativeConsume) (nativeNapi:=nativeNapi) (nativeWorker:=nativeWorker)
    (nativeWork:=nativeWork) (nativeDispatch:=nativeDispatch) trace placeholders
  · exact fun _ _ before=>Evidence.of_carrier before
  · exact fun _ _ before=>Evidence.of_account before
  · exact fun _ _ before=>Evidence.purge before
  · exact fun ledger _ _ before=>Evidence.peer ledger before
  · exact fun ledger _ _ before=>Evidence.staging ledger before
  · exact fun ledger _ _ before=>Evidence.front ledger before
  · exact fun _ _ _ before=>Evidence.of_encryption before
  · exact fun ledger _ _ _ _ _ before=>Evidence.keepalive ledger before
  · exact fun ledger pid _ _ before=>Evidence.transmit ledger pid before

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
