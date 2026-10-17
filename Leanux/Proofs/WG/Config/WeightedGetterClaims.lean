import Leanux.Proofs.WG.Config.WeightedGetterSource
import Leanux.Proofs.WG.Config.ClaimView
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- Total original mixed-width getter, including exact socket completion.
The static count includes every DATA envelope and the actual final DONE spill.
Boundary freshness refers to all earlier emitted IDs. Arbitrary endpoints and
stored bit widths use the original serializer; this asserts no global trie
ownership invariant or valid-IPv6 domain for non-32-bit stored nodes. -/
theorem mixed_weighted_getter (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace p+4) ≤ NLMSG_GOODSIZE)
    (fresh : weightedGetterFresh d p nodes ids)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (within : weightedGetterReceives d p nodes ids ≤ 4096) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (jsonPaginationResult d p
        (ids.map (fun id => dumpNodeJson (nodes id)))) ∧ s.wg.device = some d ∧
        s.wg.nlSock7 = socketReadbackFinal sock d) :=
  weightedGetter_returns pid d p nodes ids sock peers resident listed readable header nest fresh idle empty within

end Leanux.Proofs.WG.Config
