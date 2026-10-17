import Leanux.Proofs.WG.Config.WeightedPaginationSource
import Leanux.Proofs.WG.Campaign2.Bridge

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG

/-- One actual resumed callback returns its exact greedy weighted page and
preserves the Device. The supplied earlier prefix describes the original
peer list, and the cursor ID is absent from that whole prefix. No claim of
whole-getter completion, global list uniqueness or valid trie shape is made. -/
theorem mixed_resume_callback (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (before : List NodeId) (start : NodeId) (rest : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = before ++ start :: rest) (fresh : start ∉ before)
    (readable : ∀ id ∈ start :: rest, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE) :
    Campaign2.Returns (wgGetDeviceDump
      {hasWg := true, nextAllowedip := some start, allowedipsSeq := d.peerAllowedips.seq}
      d.deviceUpdateGen {}) (fun s => s.wg.device = some d)
      (fun result s => result = mixedResumeCall d p nodes start rest ∧ s.wg.device = some d) := by
  exact mixedResumeCall_returns pid d p nodes before start rest peers resident listed fresh readable header

end Leanux.Proofs.WG.Config
