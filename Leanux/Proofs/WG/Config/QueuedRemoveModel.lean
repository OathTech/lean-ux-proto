import Leanux.Proofs.WG.Config.ConfiguredOwnerModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.QueuedRemove
open Leanux Leanux.WG AllowedIps

/-- The configured endpoint only; drains may mutate resident stores. -/
def Effect (before : Device) (pid : PeerId) (after : Device) : Prop :=
  after.peerList = before.peerList.filter (· != pid) ∧
  after.peerHashtable = before.peerHashtable.filter (·.2 != pid) ∧
  ∀ t4 t6, RoutingInvariant after t4 t6 →
    ∀ e ∈ t4.entries ++ t6.entries, e.peer ≠ pid


end Leanux.Proofs.WG.Config.QueuedRemove
