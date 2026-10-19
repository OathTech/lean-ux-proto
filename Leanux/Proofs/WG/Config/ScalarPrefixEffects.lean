import Leanux.Proofs.WG.Config.ScalarPrefixModel
import Leanux.Proofs.WG.Config.EndpointAttributeSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config.ScalarPrefix
open Leanux Leanux.WG Noise Std.Do

theorem keyed_resident (d : Device) (pid : PeerId) (p : Peer) (psk : Option Key)
    (resident : d.peers[pid]? = some p) :
    (keyedDevice d pid p psk).peers[pid]? = some (keyedPeer p psk) := by
  cases psk <;> simp [keyedDevice,keyedPeer,withPeer,resident]

theorem effect_fields (d : Device) (pid : PeerId) (p : Peer) (psk : Option Key)
    (endpoint : Option EndpointAttr) (reset : Option UInt64)
    (resident : d.peers[pid]? = some p) :
    (effectDevice d pid p psk endpoint reset).peers[pid]? = some (effectPeer p psk endpoint reset) ∧
    withoutPeers (effectDevice d pid p psk endpoint reset) = withoutPeers d ∧
    (effectPeer p psk endpoint reset).presharedKey = psk.getD p.presharedKey ∧
    (effectPeer p psk endpoint reset).persistentKeepaliveInterval = p.persistentKeepaliveInterval ∧
    (effectPeer p psk endpoint reset).refcount = p.refcount ∧
    (effectPeer p psk endpoint reset).allowedipsList = p.allowedipsList := by
  have base := keyed_resident d pid p psk resident
  cases endpoint with
  | none =>
    cases psk <;> simp [effectDevice,effectPeer,keyedDevice,keyedPeer,withPeer,withoutPeers,resident]
  | some a =>
    have fields := endpointAttributeStores_fields (keyedDevice d pid p psk) pid
      (keyedPeer p psk) a reset base
    refine ⟨fields.1,?_,?_,?_,?_,?_⟩
    · exact fields.2.1.trans (by cases psk <;> rfl)
    all_goals
      cases decode : endpointAttribute a with
      | none => cases psk <;> simp [effectPeer,endpointAttributePeer,decode,keyedPeer]
      | some e =>
        cases equal : endpointSame e (keyedPeer p psk).endpoint <;> cases reset <;> cases psk <;>
          simp_all [effectPeer,endpointAttributePeer,endpointStoredPeer,keyedPeer]

end Leanux.Proofs.WG.Config.ScalarPrefix
