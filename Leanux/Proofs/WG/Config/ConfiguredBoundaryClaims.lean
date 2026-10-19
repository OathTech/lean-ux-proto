import Leanux.Proofs.WG.Config.ConfiguredBoundaryBridge
import Leanux.Proofs.WG.Config.ConfiguredRepresentationEffects
import Leanux.Proofs.WG.Config.ConfiguredOwnerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.OwnerConfiguration
open Leanux Leanux.WG AllowedIps Queues.RxCredits

/-- At an accounted configuration boundary, configured and resident ownership
hold for any exact representation of the actual endpoint. Structural uniqueness
joins the witnesses; extensional lookup agreement is not used. -/
theorem projected_entry_resident (cs : Ledger) (loans : Reservations)
    (s : Campaign2.Snapshot) (d : Device) (t4 t6 : Tree)
    (entry : ProjectedEntry cs loans s) (device : s.wg.device = some d)
    (routing : RoutingInvariant d t4 t6) :
    ConfiguredOwners d t4 t6 ∧ ResidentOwnerLists d t4 t6 := by
  obtain ⟨⟨g,a,same,input⟩,ready⟩ := entry
  subst s
  obtain ⟨out,present,u4,u6,represented,owners⟩ := ready
  have equal : out=d := Option.some.inj (present.symm.trans device)
  subst out
  have configured := configuredOwners_representation d u4 u6 t4 t6
    represented.forest routing.forest owners
  obtain ⟨holders,funded,_⟩ := input.1.1
  exact ⟨configured,funded_configuredOwners_resident g d t4 t6 holders cs loans
    device funded configured routing.lists⟩

end Leanux.Proofs.WG.Config.OwnerConfiguration

