import Leanux.Proofs.WG.Config.InitializedRoutingAccountSource
import Leanux.Proofs.WG.Configuration.InitializedJoint

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.InitializedRouting
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits AllowedIps

/-- The result projection is identity, so the source-selected account and
routing theorem concern exactly the same final World, not just equal JSON. -/
theorem account_projects (trace : Runner.Trace) (placeholders : Bool) :
    ProjectsOuter RoutingJoint.rxEvent id
      (RoutingJoint.executeTrace trace placeholders)
      (RunnerAccount.observed trace placeholders) :=
  RoutingJoint.executeTraceWith_projects RoutingJoint.rxEvent id
    RoutingJoint.syscall RxHistory.syscall (fun j w=>(j,w)) (fun j w=>(j,w))
    RoutingJoint.syscall_rx (fun _ _=>rfl) trace placeholders

def inspection (trace : Runner.Trace) (placeholders : Bool) : Inspection :=
  let result := runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []
  ⟨result.1.map (fun (json,w)=>(json,Campaign2.Product.snapshot w)),
    result.2.filterMap RoutingJoint.routingEvent⟩

theorem inspection_reached (trace : Runner.Trace) (placeholders : Bool) :
    (inspection trace placeholders).outcome =
      Index.ReachedInitialized.inspection trace placeholders := by
  have same := congrArg Prod.fst (account_projects trace placeholders [])
  simp only [List.filterMap_nil,Except.map_id,id_eq] at same
  unfold inspection Index.ReachedInitialized.inspection
  dsimp only
  rw [same]

theorem inspection_safe (trace : Runner.Trace) (shape : Configuration.TraceAddressShape trace)
    (placeholders : Bool) :
    CompletionSafe ([],[]) (inspection trace placeholders).routing :=
  (RoutingPosition.executeTrace_checks trace shape placeholders).2.2.2

theorem inspection_routing (trace : Runner.Trace) (shape : Configuration.TraceAddressShape trace)
    (placeholders : Bool) :
    match (inspection trace placeholders).outcome with
    | .error _=>True
    | .ok (_,final)=>RoutingAt (inspection trace placeholders).routing final := by
  cases run : runPrefixOuter (RoutingJoint.executeTrace trace placeholders) [] with
  | mk outcome history =>
    cases outcome with
    | error stop => simp only [inspection,run,Except.map]
    | ok out =>
      have routed := RoutingPosition.executeTrace_normal trace shape placeholders out
        (congrArg Prod.fst run)
      simpa only [inspection,run,Except.map,RoutingAt,GlobalCompletionState,
        routingView,Campaign2.Product.snapshot,Campaign2.snapshot,Campaign2.core] using routed.2


end Leanux.Proofs.WG.Config.InitializedRouting
