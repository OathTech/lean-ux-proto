import Leanux.Proofs.WG.Config.MultiMixedModel
import Leanux.Proofs.WG.Config.PeerKeyGetterModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual captured endpoint-source clearing effect preserves every peer's
serialized fields, allowed-IP list and cursor lifetime data, including absence. -/
theorem clearedPeerStore_getter_frame (d current : Device) (seen : List PeerId)
    (effect : ClearedPeerStore d current seen) :
    ∀ q : PeerId, (current.peers[q]?).map keyGetterPeerView =
      (d.peers[q]?).map keyGetterPeerView := by
  intro q
  by_cases member : q ∈ seen
  · obtain ⟨p,reset,before,after⟩ := (show ∃ p reset, d.peers[q]? = some p ∧
        current.peers[q]? = some (clearedSource p reset) by
      simpa only [ClearedPeerStore,member,ite_true] using effect q)
    rw [before,after]
    apply congrArg some
    cases endpoint : p.endpoint <;> simp [keyGetterPeerView,peerFixedAttrs,peerFixedSpace,clearedSource,endpoint]
  · have same : current.peers[q]? = d.peers[q]? := by
      simpa only [ClearedPeerStore,member,ite_false] using effect q
    rw [same]

end Leanux.Proofs.WG.Config
