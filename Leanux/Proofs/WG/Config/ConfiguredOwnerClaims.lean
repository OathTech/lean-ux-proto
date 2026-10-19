import Leanux.Proofs.WG.Config.ConfiguredOwnerSource
import Leanux.Proofs.WG.Config.RoutingReadbackSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps Queues.RxCredits

/-- Initial configured owners remain configured after every normal original
allowed-IP setter outcome, including invalid attributes and ENOMEM. -/
theorem setAllowedip_configured_owners (d : Device) (t4 t6 : Tree)
    (pid : PeerId) (p : Peer) (attrs : AllowedIpAttrs)
    (shape : AllowedIps.AddressShape attrs)
    (routing : RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6) (selected : pid ∈ d.peerList)
    (resident : d.peers[pid]? = some p) :
    Campaign2.Ensures (setAllowedip pid attrs) (fun s => s.wg.device = some d)
      (fun ret s => ∃ out u4 u6, s.wg.device = some out ∧
        AllowedipRoutingEffect d out t4 t6 pid attrs ret ∧
        RoutingInvariant out u4 u6 ∧ ConfiguredOwners out u4 u6) := by
  intro g ambient ret final after device run
  obtain ⟨out,present,effect⟩ := setAllowedip_routingEffect d t4 t6 pid p attrs
    shape routing resident g ambient ret final after device run
  obtain ⟨u4,u6,representation,configured⟩ :=
    allowedipRoutingEffect_configured d out t4 t6 pid attrs ret routing owners selected effect
  exact ⟨out,u4,u6,present,effect,representation,configured⟩


/-- The same actual setter also retains a resident owner and its list membership
for every represented entry. Initial list residency is sufficient. -/
theorem setAllowedip_resident_owners (d : Device) (t4 t6 : Tree)
    (pid : PeerId) (p : Peer) (attrs : AllowedIpAttrs)
    (shape : AllowedIps.AddressShape attrs)
    (routing : RoutingInvariant d t4 t6)
    (owners : ConfiguredOwners d t4 t6) (selected : pid ∈ d.peerList)
    (resident : d.peers[pid]? = some p)
    (listed : ∀ q ∈ d.peerList, ∃ p, d.peers[q]? = some p) :
    Campaign2.Ensures (setAllowedip pid attrs) (fun s => s.wg.device = some d)
      (fun ret s => ∃ out u4 u6, s.wg.device = some out ∧
        AllowedipRoutingEffect d out t4 t6 pid attrs ret ∧
        RoutingInvariant out u4 u6 ∧ ConfiguredOwners out u4 u6 ∧
        ResidentOwnerLists out u4 u6) := by
  intro g ambient ret final after device run
  obtain ⟨out,u4,u6,present,effect,representation,configured⟩ :=
    setAllowedip_configured_owners d t4 t6 pid p attrs shape routing owners selected resident
      g ambient ret final after device run
  exact ⟨out,u4,u6,present,effect,representation,configured,
    configuredOwners_resident out u4 u6 configured
      (allowedipRoutingEffect_listed d out t4 t6 pid attrs ret listed effect) representation.lists⟩


end Leanux.Proofs.WG.Config
