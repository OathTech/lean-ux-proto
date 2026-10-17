import Leanux.Proofs.WG.Config.EndpointSetEffects
import Leanux.Proofs.WG.Config.PeerKeyGetterModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Cache reset timestamps do not change any serialized or cursor-lifetime
field of the effective endpoint update. -/
theorem endpointAttributePeer_getter_frame (p : Peer) (a : EndpointAttr)
    (reset : Option UInt64) :
    keyGetterPeerView (endpointAttributePeer p a reset) =
      keyGetterPeerView (endpointApplied p a) := by
  cases decoded : endpointAttribute a with
  | none => simp only [endpointAttributePeer,endpointApplied,decoded]
  | some e =>
    cases equal : endpointSame e p.endpoint <;> cases reset <;>
      simp only [endpointAttributePeer,endpointApplied,decoded,endpointStoredPeer,
        equal,Bool.false_eq_true,reduceIte,keyGetterPeerView,peerFixedAttrs,peerFixedSpace]

/-- Varying only the recorded endpoint-cache reset preserves the getter's
entire resident projection and every non-peer Device field. -/
theorem endpointSetter_getter_frame (d : Device) (pid : PeerId) (p : Peer)
    (a : EndpointAttr) (reset : Option UInt64) :
    withoutPeers (endpointSetterDevice d pid p a reset) =
      withoutPeers (endpointSetterDevice d pid p a none) ∧
    ∀ q : PeerId, ((endpointSetterDevice d pid p a reset).peers[q]?).map keyGetterPeerView =
      ((endpointSetterDevice d pid p a none).peers[q]?).map keyGetterPeerView := by
  constructor
  · exact (endpointSetter_fields d pid p a reset).1.trans
      (endpointSetter_fields d pid p a none).1.symm
  · intro q
    by_cases equal : q = pid
    · subst q
      rw [(endpointSetter_fields d pid p a reset).2.1,
        (endpointSetter_fields d pid p a none).2.1]
      simp only [Option.map_some,endpointAttributePeer_getter_frame]
    · cases decoded : endpointAttribute a with
      | none =>
        simp [endpointSetterDevice,endpointAttributeStores,decoded,withPeer,
          Std.TreeMap.getElem?_insert,Ne.symm equal]
      | some e =>
        cases same : endpointSame e p.endpoint <;> cases reset <;>
          simp [endpointSetterDevice,endpointAttributeStores,decoded,endpointStores,
            same,withPeer,Std.TreeMap.getElem?_insert,Ne.symm equal]

/-- The ordered endpoint stores preserve every other peer lookup. -/
theorem endpointSetter_other (d : Device) (pid q : PeerId) (p : Peer)
    (a : EndpointAttr) (reset : Option UInt64) (different : q ≠ pid) :
    (endpointSetterDevice d pid p a reset).peers[q]? = d.peers[q]? := by
  cases decoded : endpointAttribute a with
  | none =>
    simp [endpointSetterDevice,endpointAttributeStores,decoded,withPeer,
      Std.TreeMap.getElem?_insert,Ne.symm different]
  | some e =>
    cases same : endpointSame e p.endpoint <;> cases reset <;>
      simp [endpointSetterDevice,endpointAttributeStores,decoded,endpointStores,
        same,withPeer,Std.TreeMap.getElem?_insert,Ne.symm different]

end Leanux.Proofs.WG.Config
