import Leanux.Proofs.WG.Config.KeyReadbackModel
import Leanux.Proofs.WG.Config.MultiPeerDumpModel

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Readback, capacity and cursor lifetime data unchanged by quiet key expiry. -/
def keyGetterPeerView (p : Peer) :=
  (p.remoteStatic, peerFixedAttrs p, peerFixedSpace p, p.allowedipsList, p.refcount, p.isDead)

/-- Actual successor residents on the original peer list; outside that list
the supplied total view is retained. Resident proofs discharge the fallback. -/
def keyGetterPeers (base current : Device) (peers : PeerId → Peer) (q : PeerId) : Peer :=
  if q ∈ base.peerList then (current.peers[q]?).getD (peers q) else peers q

end Leanux.Proofs.WG.Config
