import Leanux.Proofs.WG.Config.ConfiguredBoundaryBridge
import Leanux.Proofs.WG.AllowedIps.RoutingInitial
import Leanux.Proofs.WG.AllowedIps.RoutingEnvTrafficFrames
import Leanux.Proofs.WG.Queues.BaseCoherenceCalls
import Leanux.Proofs.WG.AllowedIps.RoutingEnvControlsCompletion

import Leanux.Proofs.WG.Config.ConfiguredOptionalModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG Noise AllowedIps Queues Queues.RxCredits
open Leanux.Proofs.Framing Leanux.Proofs.Logged Lifetimes Std.Do

theorem optionalReady_retains (g v : WGWorld)
    (routing : RetainsRouting (routingView g) (routingView v))
    (base : BaseCoherence.slots v = BaseCoherence.slots g)
    (pre : OptionalReady g) : OptionalReady v := by
  intro out final
  cases initial : g.dev with
  | none =>
    simp only [routingView,initial,final,Option.map_none,Option.map_some,RetainsRouting] at routing
  | some d =>
    obtain ⟨t4,t6,represented,owners⟩ := pre d initial
    have kept : (routingState d).Retains (routingState out) := by
      simpa only [routingView,initial,final,Option.map_some,RetainsRouting] using routing
    have same : out.peerList = d.peerList := by
      simpa only [BaseCoherence.slots,initial,final,Option.map_some,Option.getD_some] using base
    exact ⟨t4,t6,represented.of_retains kept,
      configured_of_list d out t4 t6 owners (fun _ member => same.symm ▸ member)⟩

theorem optionalReady_initial (net bare : Bool) :
    OptionalReady (Runner.initialWG net bare) := by
  intro d device
  cases net <;> cases bare
  all_goals simp only [Runner.initialWG,Bool.not_false,Bool.not_true,
    Bool.false_and,Bool.true_and,Bool.false_eq_true,ite_false,ite_true] at device
  all_goals first
    | cases device
    | skip
  refine ⟨.empty,.empty,empty_routing 3 "wg0",?_⟩
  intro e member
  simp only [Tree.entries,List.append_nil,List.not_mem_nil] at member

end Leanux.Proofs.WG.Config.OwnerConfiguration
