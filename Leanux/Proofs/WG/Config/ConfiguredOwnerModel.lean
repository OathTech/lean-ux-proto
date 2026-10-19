import Leanux.Proofs.WG.Config.RoutingReadbackModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps

/-- Every represented allowed-IP owner is in the configured peer list.
This is a boundary invariant; peer removal unlinks before removing its routes. -/
def ConfiguredOwners (d : Device) (t4 t6 : Tree) : Prop :=
  ∀ e ∈ t4.entries ++ t6.entries, e.peer ∈ d.peerList

/-- Actual owner residency and exact node membership, for both families. -/
def ResidentOwnerLists (d : Device) (t4 t6 : Tree) : Prop :=
  ∀ e ∈ t4.entries ++ t6.entries, ∃ p,
    d.peers[e.peer]? = some p ∧ e.id ∈ p.allowedipsList


end Leanux.Proofs.WG.Config
