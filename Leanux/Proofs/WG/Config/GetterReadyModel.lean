import Leanux.Proofs.WG.Config.RoutingReadbackModel

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG AllowedIps

/-- Total lookup used only by the proof-side serializer. Readability establishes
that its fallback is never used for a configured occurrence. -/
def routingReadPeer (d : Device) (pid : PeerId) : Peer :=
  (d.peers[pid]?).getD {remoteStatic:=[],presharedKey:=[],precomputedStaticStatic:=[],internalId:=0}

def DeviceDumpReadable (d : Device) : Prop :=
  d.peerList.Nodup ∧
  (∀ pid ∈ d.peerList,d.peers[pid]?=some (routingReadPeer d pid)) ∧
  (∀ pid ∈ d.peerList,(routingReadPeer d pid).allowedipsList.Nodup) ∧
  ∀ pid ∈ d.peerList,∀ id ∈ (routingReadPeer d pid).allowedipsList,
    d.nodes[id]?=some (routingReadNode d id)

end Leanux.Proofs.WG.Config
