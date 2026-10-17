import Leanux.Proofs.WG.Config.EndpointAttributeSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Consequences of the ordered acquire/update/release stores. The original
reference count is restored; cache timestamps do not alter serialized fields. -/
theorem endpointSetter_fields (d : Device) (pid : PeerId) (p : Peer) (a : EndpointAttr)
    (reset : Option UInt64) :
    withoutPeers (endpointSetterDevice d pid p a reset) = withoutPeers d ∧
    (endpointSetterDevice d pid p a reset).peers[pid]? = some (endpointAttributePeer p a reset) ∧
    (endpointAttributePeer p a reset).allowedipsList = p.allowedipsList ∧
    peerFixedAttrs (endpointAttributePeer p a reset) = peerFixedAttrs (endpointApplied p a) ∧
    peerFixedSpace (endpointAttributePeer p a reset) = peerFixedSpace (endpointApplied p a) := by
  cases decoded : endpointAttribute a with
  | none => simp [endpointSetterDevice, endpointAttributeStores, endpointAttributePeer,
      endpointApplied, decoded, withPeer, withoutPeers]
  | some e =>
    cases equal : endpointSame e p.endpoint <;> cases reset <;>
      simp [endpointSetterDevice, endpointAttributeStores, endpointAttributePeer, endpointApplied,
        decoded, endpointStores, endpointStoredPeer, equal, withPeer, withoutPeers,
        peerFixedAttrs, peerFixedSpace]

end Leanux.Proofs.WG.Config
