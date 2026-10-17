import Leanux.Proofs.WG.Config.MultiPeerScalarModel
import Leanux.Proofs.WG.Config.ScalarGetterSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Lean

/-- The ordered scalar writes retain every original peer/node occurrence,
while every listed occurrence of the target reads its configured scalar value. -/
theorem scalarRequestDevice_mixed_effect (d : Device) (peers : PeerId → Peer)
    (pid : PeerId) (psk : Key) (interval : Nat)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q)) :
    let updated := scalarRequestDevice d pid (peers pid) psk interval
    let configured := scalarPeerView peers pid psk interval
    updated.peerList = d.peerList ∧ updated.ifname = d.ifname ∧
    updated.ifindex = d.ifindex ∧ updated.nodes = d.nodes ∧
    (∀ q ∈ updated.peerList, updated.peers[q]? = some (configured q)) ∧
    (∀ q, (configured q).allowedipsList = (peers q).allowedipsList) := by
  dsimp only [scalarRequestDevice,scalarDevice,withPeer]
  refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
  · intro q member
    by_cases same : q = pid
    · subst q
      simp [scalarPeerView]
    · simpa [scalarPeerView,Std.TreeMap.getElem?_insert,same,Ne.symm same] using residents q member
  · intro q
    by_cases same : q = pid
    · subst q; simp [scalarPeerView]
    · simp [scalarPeerView,same]

end Leanux.Proofs.WG.Config
