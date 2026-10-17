import Leanux.Proofs.WG.Config.MultiPeerScalarModel
import Leanux.Proofs.WG.Config.ScalarGetterFrames

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Substantive transport through the ordered peer-map writes: all list
occurrences still read the selected scalar update or their original peer. -/
theorem scalarRequestDevice_dump_effect (d : Device) (peers : PeerId → Peer)
    (pid : PeerId) (psk : Key) (interval : Nat)
    (residents : ∀ q ∈ d.peerList, d.peers[q]? = some (peers q))
    (emptyIps : ∀ q ∈ d.peerList, (peers q).allowedipsList = []) :
    let updated := scalarRequestDevice d pid (peers pid) psk interval
    let configured := scalarPeerView peers pid psk interval
    updated.peerList = d.peerList ∧ updated.ifname = d.ifname ∧
    updated.ifindex = d.ifindex ∧ devicePrefixSpace updated = devicePrefixSpace d ∧
    (∀ q ∈ updated.peerList, updated.peers[q]? = some (configured q)) ∧
    (∀ q ∈ updated.peerList, (configured q).allowedipsList = []) := by
  dsimp only [scalarRequestDevice,scalarDevice,withPeer]
  refine ⟨rfl,rfl,rfl,rfl,?_,?_⟩
  · intro q member
    by_cases same : q = pid
    · subst q
      simp [scalarPeerView]
    · simpa [scalarPeerView,Std.TreeMap.getElem?_insert,same,Ne.symm same]
        using residents q member
  · intro q member
    by_cases same : q = pid
    · subst q
      simpa [scalarPeerView] using emptyIps pid member
    · simpa [scalarPeerView,same] using emptyIps q member


end Leanux.Proofs.WG.Config
