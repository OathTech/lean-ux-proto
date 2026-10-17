import Leanux.Proofs.WG.Config.PaginationCountModel
import Leanux.Proofs.WG.Config.PaginationManyClaims
import Leanux.Proofs.WG.Config.PaginationSingleSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual getter returns all allowed-IP occurrences in order for any
finite IPv4 list in this single-peer domain. Canonical boundaries use the
actual first-occurrence cursor search, and the precise envelope count includes
DATA and any separate DONE. The whole initial Device is retained. -/
theorem ipv4Pagination_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids) (fresh : ipv4PaginationFresh d ids)
    (readable : Ipv4Residents d nodes ids) (endpoint : p.endpoint = none)
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (enough : ipv4PaginationReceiveCount d ids ≤ 4096) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (suffixJson d p nodes ids) ∧
        s.wg.device = some d ∧ s.wg.nlSock7 = socketReadbackFinal sock d) := by
  cases ids with
  | nil =>
    exact wgGetDevice_ipv4_single_returns pid d p nodes [] sock peers resident listed readable
      endpoint room (Nat.zero_le _) idle empty
  | cons first rest =>
    by_cases fits : (first :: rest).length ≤ ipv4FirstCapacity d
    · exact wgGetDevice_ipv4_single_returns pid d p nodes (first :: rest) sock peers resident
        listed readable endpoint room fits idle empty
    · exact ipv4Pagination_many_returns pid d p nodes first rest sock peers resident listed fresh
        readable endpoint room (by omega) idle empty
        (by simpa only [ipv4PaginationReceiveCount,fits,ite_false] using enough)

end Leanux.Proofs.WG.Config
