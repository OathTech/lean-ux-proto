import Leanux.Proofs.WG.Config.WeightedStartSource
import Leanux.Proofs.WG.Config.ClaimView
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- One original first callback returns exact mixed-width DATA. The weak room
domain allows a nonempty list to split before its first node, while an empty
list takes the distinct no-allowed-IP-attribute path. -/
theorem mixed_first_callback (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace p + 4) ≤ NLMSG_GOODSIZE) :
    Campaign2.Returns (wgGetDeviceDump {hasWg := true} 0 {}) (fun s => s.wg.device = some d)
      (fun result s => result = mixedFirstCall d p nodes ids ∧ s.wg.device = some d) :=
  mixedFirstCall_returns pid d p nodes ids peers resident listed readable header nest

/-- Original start returns the exact first socket state, including the
completed-DATA DONE room test. This does not execute the receive loop, infer
boundary freshness, or claim that an entire getter finishes. -/
theorem mixed_dump_start (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace p + 4) ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Campaign2.Returns (netlinkDumpStart 7 (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun _ s => s.wg.device = some d ∧ s.wg.nlSock7 = mixedStartedSocket sock (mixedFirstCall d p nodes ids)) :=
  netlinkDumpStart_mixed_returns pid d p nodes ids sock peers resident listed readable header nest idle empty

end Leanux.Proofs.WG.Config
