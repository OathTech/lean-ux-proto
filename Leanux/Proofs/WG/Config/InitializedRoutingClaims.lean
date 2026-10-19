import Leanux.Proofs.WG.Config.InitializedRoutingSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.InitializedRouting
open Lean Leanux Leanux.WG Leanux.Proofs.Logged
open Lifetimes Queues Queues.RxCredits AllowedIps

theorem inspection_json (trace : Runner.Trace) (placeholders : Bool) :
    (inspection trace placeholders).outcome.map Prod.fst =
      Runner.executeTrace trace placeholders := by
  rw [inspection_reached]
  exact Index.ReachedInitialized.inspection_json trace placeholders

/-- A normal initialized return supplies routing representation, base
residency/coherence, the established index invariant and exact residual account.
The remaining route-owner-to-base relation is not a consequence asserted here. -/
theorem normal (trace : Runner.Trace) (shape : Configuration.TraceAddressShape trace)
    (placeholders : Bool) (json : Json) (final : Campaign2.Product.Snapshot)
    (run : (inspection trace placeholders).outcome=.ok (json,final)) :
    CompletionSafe ([],[]) (inspection trace placeholders).routing ∧
    RoutingAt (inspection trace placeholders).routing final ∧ BaseReady final ∧
    Index.View.IndexCore final.toSnapshot ∧
    Index.InitializedBounds.EndpointSafe final.toSnapshot ∧
    Index.ReachedInitialized.ActualAccount trace placeholders json final := by
  have same : Index.ReachedInitialized.inspection trace placeholders=.ok (json,final) :=
    (inspection_reached trace placeholders).symm.trans run
  have facts := Index.ReachedInitialized.normal trace placeholders json final same
  exact ⟨inspection_safe trace shape placeholders,
    by simpa only [run] using inspection_routing trace shape placeholders,
    account_base facts.2,facts.1,facts.2.bounds,facts.2⟩

theorem accepted (trace : Runner.Trace) (shape : Configuration.TraceAddressShape trace)
    (placeholders : Bool) (json : Json)
    (run : Runner.executeTrace trace placeholders=.ok json) :
    ∃ final, (inspection trace placeholders).outcome=.ok (json,final) ∧
      CompletionSafe ([],[]) (inspection trace placeholders).routing ∧
      RoutingAt (inspection trace placeholders).routing final ∧ BaseReady final ∧
      Index.View.IndexCore final.toSnapshot ∧
      Index.InitializedBounds.EndpointSafe final.toSnapshot ∧
      Index.ReachedInitialized.ActualAccount trace placeholders json final := by
  obtain ⟨final,actual,_⟩ := Index.ReachedInitialized.accepted trace placeholders json run
  have same := (inspection_reached trace placeholders).trans actual
  exact ⟨final,same,normal trace shape placeholders json final same⟩

theorem parsed_accepted (input : Json) (trace : Runner.Trace)
    (parsed : Runner.parseTrace input=.ok trace) (placeholders : Bool) (json : Json)
    (run : Runner.executeTrace trace placeholders=.ok json) :
    ∃ final, (inspection trace placeholders).outcome=.ok (json,final) ∧
      CompletionSafe ([],[]) (inspection trace placeholders).routing ∧
      RoutingAt (inspection trace placeholders).routing final ∧ BaseReady final ∧
      Index.View.IndexCore final.toSnapshot ∧
      Index.InitializedBounds.EndpointSafe final.toSnapshot ∧
      Index.ReachedInitialized.ActualAccount trace placeholders json final :=
  accepted trace (Configuration.parseTrace_shape input trace parsed) placeholders json run

end Leanux.Proofs.WG.Config.InitializedRouting
