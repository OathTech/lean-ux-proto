import Leanux.Proofs.WG.Config.RoutingReadbackEffects
import Leanux.Proofs.WG.AllowedIps.ConfigurationInputs
import Leanux.Proofs.WG.Config.MixedPeerSerializerSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise

/-- The actual setter guard and selected insertion supply the pure outcome;
no final representation or successful allocation is assumed. -/
theorem setAllowedip_routingEffect (d : Device) (t4 t6 : AllowedIps.Tree)
    (pid : PeerId) (p : Peer) (attrs : AllowedIpAttrs)
    (shape : AllowedIps.AddressShape attrs)
    (routing : AllowedIps.RoutingInvariant d t4 t6)
    (resident : d.peers[pid]? = some p) :
    Noise.Ensures (setAllowedip pid attrs) (fun g => g.dev = some d)
      (fun ret g => ∃ out, g.dev = some out ∧
        AllowedipRoutingEffect d out t4 t6 pid attrs ret) := by
  intro g ambient ret final after device run
  rcases AllowedIps.setAllowedip_outcome pid attrs shape g final ambient after ret run with
    ⟨rejected, same⟩ | ⟨v4, cut, input, same, family, width, cidr, inserted⟩
  · exact ⟨d, (congrArg Framing.WGStoreView.dev same).trans device, .inl ⟨rejected,rfl⟩⟩
  · have cutDevice : cut.dev = some d := (congrArg Framing.WGStoreView.dev same).trans device
    have familyBool : ((if v4 then 4 else 6 : Nat) == 4) = v4 := by
      cases v4 <;> rfl
    obtain ⟨out, native, effect⟩ := AllowedIps.insert_routing_outcome cut final input after d cutDevice
      (if v4 then 4 else 6) (attrs.addr.getD 0) (attrs.cidr.getD 0) pid p resident t4 t6 routing
      (by simpa only [familyBool] using width) (by simpa only [familyBool] using cidr) ret inserted
    refine ⟨out, congrArg WGWorld.dev native, .inr ⟨v4,family,width,cidr,?_⟩⟩
    simpa only [familyBool] using effect

end Leanux.Proofs.WG.Config
