import Leanux.Proofs.WG.AuthenticatedEffects.StagedCompleteReachedNativeCutConsequences

/-! The concrete source composition eliminates its extension parameters.
These equalities check that no leaf family supplied by a caller remains in
the initialized relation. They do not replace the native source audit. -/
namespace Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
open Leanux Leanux.WG Leanux.Proofs.Logged TransmitSecurity CausalJournal

theorem consume_closed (left right : Consume.Points.ChildPoints) :
    WorkService.Composition.consumePoints (StagingExpanded.consumePoints left)=
      WorkService.Composition.consumePoints (StagingExpanded.consumePoints right) := by
  funext token w h u middle
  cases token <;> rfl

theorem napi_closed (left right : Consume.Points.ChildPoints) (front back : Napi.Points.ChildPoints) :
    TrafficConcrete.napiPoints left front=TrafficConcrete.napiPoints right back := by
  unfold TrafficConcrete.napiPoints ReceiveWorker.Composition.napiPoints
  rw [consume_closed left right]
  funext token w h u middle
  cases token <;> rfl

theorem work_closed (left right : WorkService.Points.ChildPoints) :
    Service.Expanded.workPoints (ProtocolSend.workPoints left)=
      Service.Expanded.workPoints (ProtocolSend.workPoints right) := by
  funext token w h u middle
  cases token <;> rfl

def iterations (consume : Consume.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (worker : Iteration.Points.ChildPoints) : Iteration.Points.ChildPoints :=
  Napi.Composition.iterationPoints (TrafficConcrete.napiPoints consume napi)
    (ReceiveWorker.Composition.baseWorkerPoints
      (Prepare.Points.iterationPoints (EncryptionCallback.iterationPoints (TrafficConcrete.workerPoints worker))))

theorem iterations_closed (c d : Consume.Points.ChildPoints) (n m : Napi.Points.ChildPoints)
    (w x : Iteration.Points.ChildPoints) : iterations c n w=iterations d m x := by
  unfold iterations
  rw [napi_closed c d n m]
  funext token world h u middle
  cases token <;> rfl

theorem scheduler_closed (c d : Consume.Points.ChildPoints) (n m : Napi.Points.ChildPoints)
    (w x : Iteration.Points.ChildPoints) :
    Service.ReceiveComposition.schedulerPoints c (IPv6.napiPoints (RoutedTransmit.napiPoints n)) (TrafficConcrete.workerPoints w)=
      Service.ReceiveComposition.schedulerPoints d (IPv6.napiPoints (RoutedTransmit.napiPoints m)) (TrafficConcrete.workerPoints x) := by
  change Iteration.Points.schedulerPoints (iterations c n w) (Napi.Composition.napiPoints (TrafficConcrete.napiPoints c n)) =
    Iteration.Points.schedulerPoints (iterations d m x) (Napi.Composition.napiPoints (TrafficConcrete.napiPoints d m))
  rw [iterations_closed c d n m w x,napi_closed c d n m]

theorem services_closed (c d : Consume.Points.ChildPoints) (n m : Napi.Points.ChildPoints)
    (w x : Iteration.Points.ChildPoints) (r s : WorkService.Points.ChildPoints) :
    TrafficConcrete.servicePoints c n w r=TrafficConcrete.servicePoints d m x s := by
  unfold TrafficConcrete.servicePoints Service.ReceiveComposition.servicePoints
  rw [scheduler_closed c d n m w x,work_closed r s]

def dispatch (service : Service.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (other : Dispatch.Points.ChildPoints) : Dispatch.Points.ChildPoints :=
  Service.Composition.dispatchPoints service
    (Lifecycle.Concrete.dispatchPoints (DumpConcrete.dispatchPoints (XmitConcrete.dispatchPoints
      (TrafficConcrete.dispatchPoints service napi (ConfigConcrete.dispatchPoints other)))))

theorem dispatch_closed (service : Service.Points.ChildPoints) (napi : Napi.Points.ChildPoints)
    (left right : Dispatch.Points.ChildPoints) : dispatch service napi left=dispatch service napi right := by
  funext α action token w h u middle
  cases token with
  | family kind => cases kind <;> rfl

theorem children_closed (c d : Consume.Points.ChildPoints) (n m : Napi.Points.ChildPoints)
    (w x : Iteration.Points.ChildPoints) (r s : WorkService.Points.ChildPoints)
    (left right : Dispatch.Points.ChildPoints) :
    children c n w r left=children d m x s right := by
  unfold children
  rw [services_closed c d n m w x r s,napi_closed c d n m]
  funext α action token world h u middle
  cases token with
  | dispatch call =>
      change (∃ site,Dispatch.Points.Point (dispatch (TrafficConcrete.servicePoints d m x s)
        (TrafficConcrete.napiPoints d m) left) (Dispatch.Points.canonical call) world h site u middle) = _
      rw [dispatch_closed _ _ left right]
      rfl
  | sends => rfl
  | idle => rfl
  | afterXmit => rfl
  | advance => rfl

/-- The initialized source relation uses only the concrete child families.
The extension slots are eliminated by children_closed, not assumed safe. -/
def concreteChildren : Runner.Points.ChildPoints :=
  children (fun _ _ _ _ _=>False) (fun _ _ _ _ _=>False)
    (fun _ _ _ _ _=>False) (fun _ _ _ _ _=>False) (fun _ _ _ _ _ _ _=>False)

theorem concrete_children (c : Consume.Points.ChildPoints) (n : Napi.Points.ChildPoints)
    (w : Iteration.Points.ChildPoints) (r : WorkService.Points.ChildPoints)
    (dispatch : Dispatch.Points.ChildPoints) : children c n w r dispatch=concreteChildren :=
  children_closed _ _ _ _ _ _ _ _ _ _

/-- A point of the original initialized runner with every child source fixed.
Only the actual source prefixes and their native state/history are parameters. -/
def SourcePoint (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (site : Runner.Points.Site) (w : World) (h : List Event) : Prop :=
  Runner.Points.Point concreteChildren (Runner.Points.executeShape trace placeholders) [] site w h

/-- Security: each declared initialized `SourcePoint` admits a ticket/cell
account, either immediately or after its original pending records on the same
WG state. The ledger is existential at that point; source-cut coverage is an
audit obligation. No extension family or incoming certificate is supplied. -/
theorem initialized_concrete_account (trace : Leanux.Runner.Trace) (placeholders : Bool)
    (point : SourcePoint trace placeholders site w h) : AccountOrRecords h w.wg :=
  initialized_account_or_records trace placeholders site w h point

end Leanux.Proofs.WG.AuthenticatedEffects.StagedEntry.Reached.NativeAccounting
