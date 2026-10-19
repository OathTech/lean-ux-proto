import Leanux.Proofs.WG.Index.ReachedInitializedModel
import Leanux.Proofs.WG.AllowedIps.RoutingGlobal

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.InitializedRouting
open Lean Leanux Leanux.WG AllowedIps

/-- The existing joint runner, projected without discarding routing completions
on an indexed Stop. An error has no final snapshot. -/
structure Inspection where
  outcome : Index.ReachedInitialized.Inspection
  routing : List RoutingCompletion

/-- Semantic routing at the actual final snapshot. This is deliberately not
the unproved relation that every route owner belongs to the live base list. -/
def RoutingAt (history : List RoutingCompletion) (final : Campaign2.Product.Snapshot) : Prop :=
  GlobalRoutedView (final.wg.device.map routingState) (completionFold history ([],[]))

/-- Base-list and pubkey-table coherence, plus residency of every listed
occurrence. These facts do not assert residency of raw routing owner labels. -/
structure BaseReady (final : Campaign2.Product.Snapshot) : Prop where
  coherent : ∀ d, final.wg.device=some d →
    d.peerList.Nodup ∧ ∀ row ∈ d.peerHashtable, row.2 ∈ d.peerList
  residents : ∀ d, final.wg.device=some d → ∀ pid ∈ d.peerList,
    ∃ p, d.peers[pid]?=some p


end Leanux.Proofs.WG.Config.InitializedRouting
