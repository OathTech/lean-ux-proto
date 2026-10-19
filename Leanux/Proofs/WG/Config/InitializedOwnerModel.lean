import Leanux.Proofs.WG.Config.ConfiguredOptionalModel
import Leanux.Proofs.WG.Config.InitializedRoutingModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.InitializedOwner
open Leanux Leanux.WG AllowedIps

/-- Every present initialized endpoint has an exact routing representation.
Every such representation has configured, resident owners with node-list membership. -/
def OwnershipAt (final : Campaign2.Product.Snapshot) : Prop :=
  ∀ d, final.wg.device=some d →
    (∃ t4 t6, RoutingInvariant d t4 t6) ∧
    ∀ t4 t6, RoutingInvariant d t4 t6 →
      ConfiguredOwners d t4 t6 ∧ ResidentOwnerLists d t4 t6

end Leanux.Proofs.WG.Config.InitializedOwner
