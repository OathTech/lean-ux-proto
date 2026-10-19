import Leanux.Proofs.WG.Config.RequestInputModel
import Leanux.Proofs.WG.Config.MultiMixedModel
import Leanux.Proofs.WG.Config.PeerKeyGetterModel
import Leanux.Proofs.WG.Config.MixedPageDeviceModel
import Leanux.Proofs.WG.Config.MixedGetterModel
import Leanux.Proofs.WG.Config.SocketReadbackModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

namespace RequestOrder

/-- Readback of the committed request prefix, with the actual cursor-effect
device and its successor peer serialization values. Cached local sources may
have changed before readback. -/
def MixedRefusalReadback (attrs : DeviceAttrs) (d : Device)
    (peers : PeerId → Peer) (nodes : NodeId → AipNode) (sock : NlSock)
    (pages : List MixedPeerScan) (dump : Except Int Json) (final : Campaign2.Snapshot) : Prop :=
  dump = .ok (mixedGetterJson (prefixDevice attrs d) peers nodes) ∧
  ∃ current, ∃ values : PeerId → Peer,
    withoutPeers current = withoutPeers (prefixDevice attrs d) ∧
    ClearedPeerStore d current d.peerList ∧
    (∀ q ∈ d.peerList,current.peers[q]? = some (values q)) ∧
    (∀ q,keyGetterPeerView (values q) = keyGetterPeerView (peers q)) ∧
    final.wg.device = some (mixedPagesDevice current pages) ∧
    final.wg.nlSock7 = socketReadbackFinal sock current ∧
    CursorHeld current (mixedPagesDevice current pages) none

end RequestOrder

end Leanux.Proofs.WG.Config
