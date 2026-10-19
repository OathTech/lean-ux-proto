import Leanux.Proofs.WG.Queues.JointRunner
import Leanux.Proofs.WG.Queues.RxLinkRunner
import Leanux.Proofs.WG.Origins.OwnerRunner
import Leanux.Proofs.WG.Configuration.RunnerRouting

/-! The existing initialized joint execution has one journal. Its exact
projections retain current/owner checks, source linkage and routing completion
safety, including indexed Stops. Positional routing at a captured packet state
is a separate contract and is not inferred from the final routing state. -/
namespace Leanux.Proofs.WG.RoutingPosition
open Leanux Leanux.WG Leanux.Proofs.Logged
open Queues AllowedIps Configuration

/-- Owner checks do not require routing address-shape evidence. -/
theorem executeTrace_owner (trace : Runner.Trace) (placeholders : Bool) :
    OwnerChecks.Safe ((runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2.filterMap
      RoutingJoint.rxEvent) := by
  have rx := congrArg Prod.snd (RoutingJoint.executeTrace_rx trace placeholders [])
  simp only [List.filterMap_nil] at rx
  rw [← rx]
  exact OwnerRunner.executeTrace trace placeholders

/-- The actual two projections refer to this same initialized joint execution.
Address shape is the existing routing premise; no packet authorization is assumed. -/
theorem executeTrace_checks (trace : Runner.Trace) (shape : TraceAddressShape trace)
    (placeholders : Bool) :
    let h := (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2
    OwnerChecks.Safe (h.filterMap RoutingJoint.rxEvent) ∧
    RxLink.HistoryLinked (h.filterMap RoutingJoint.rxEvent) ∧
    RxLink.HistoryReceiptsValid (h.filterMap RoutingJoint.rxEvent) ∧
    CompletionSafe ([],[]) (h.filterMap RoutingJoint.routingEvent) := by
  have rx := congrArg Prod.snd (RoutingJoint.executeTrace_rx trace placeholders [])
  have routing := congrArg Prod.snd (RoutingJoint.executeTrace_routing trace placeholders [])
  simp only [List.filterMap_nil] at rx routing
  have owner := OwnerRunner.executeTrace trace placeholders
  have links := RxLink.executeTraceHistory_linkage trace placeholders
  have routes := (executeTraceObserved_routing trace shape placeholders).1
  rw [rx] at owner links
  rw [routing] at routes
  exact ⟨owner,links.1,links.2,routes⟩

/-- Only a normal result supplies a final World. This is an endpoint theorem,
not evidence of routing at any earlier captured packet cut. -/
theorem executeTrace_normal (trace : Runner.Trace) (shape : TraceAddressShape trace)
    (placeholders : Bool) (out : Lean.Json × World)
    (normal : (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).1 = .ok out) :
    GlobalCompletionState ([],[])
      ((runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2.filterMap RoutingJoint.routingEvent)
      out.2.wg := by
  have projected := RoutingJoint.executeTrace_routing trace placeholders []
  have result := congrArg Prod.fst projected
  have history := congrArg Prod.snd projected
  simp only [List.filterMap_nil,normal,Except.map,id_eq] at result history
  have state := (executeTraceObserved_routing trace shape placeholders).2 out result
  rwa [history] at state

/-- A selected occurrence keeps the exact strict earlier RX projection,
regardless of interleaved routing completions or equal receipt values. -/
theorem decrypt (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RoutingJoint.Event) (id : SkbId)
    (r : WGRunWitness (RxPacket × Option RxPacket))
    (position : (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 =
      pre ++ .rx (.rx (.decrypt id r)) :: post) :
    CurrentLifecycle.Inv (Origins.HistorySupport.sessions (pre.filterMap RoutingJoint.rxEvent)) r.before ∧
    OwnerBounds.Carrier r.before := by
  have safe := executeTrace_owner trace placeholders
  apply safe.decrypt (id := id) (pre := pre.filterMap RoutingJoint.rxEvent) (post := post.filterMap RoutingJoint.rxEvent)
  simp only [position,List.filterMap_append,List.filterMap_cons,RoutingJoint.rxEvent]

/-- The copied probe retains its own captured state and the actual earlier
RX allocation history; projection does not turn it into committed execution. -/
theorem probe (trace : Runner.Trace) (placeholders : Bool)
    (pre post : List RoutingJoint.Event) (p : Lifetimes.ProbeEntry)
    (position : (runPrefixOuter (RoutingJoint.executeTrace trace placeholders) []).2 =
      pre ++ .rx (.audit (.probe p)) :: post) :
    p.history = RxHistory.prior (pre.filterMap RoutingJoint.rxEvent) ∧
    CurrentSessionPrefix.StateInv (pre.filterMap RoutingJoint.rxEvent) p.world ∧
    OwnerBounds.Carrier p.world.wg := by
  have safe := executeTrace_owner trace placeholders
  apply safe.probe (pre := pre.filterMap RoutingJoint.rxEvent) (post := post.filterMap RoutingJoint.rxEvent)
  simp only [position,List.filterMap_append,List.filterMap_cons,RoutingJoint.rxEvent]

end Leanux.Proofs.WG.RoutingPosition
