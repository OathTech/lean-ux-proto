import Leanux.Proofs.WG.Config.PaginationChainSource
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- Any finite number of actual IPv4 pages on the multi-page branch of the
original getter. The only uniqueness condition is first-occurrence cursor
freshness at calculated boundaries, and the bound counts actual receive
envelopes, including a separate DONE. -/
theorem ipv4Pagination_many_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (first : NodeId) (rest : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = first :: rest)
    (fresh : ipv4PaginationFresh d (first :: rest))
    (readable : Ipv4Residents d nodes (first :: rest)) (endpoint : p.endpoint = none)
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (many : ipv4FirstCapacity d < (first :: rest).length)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (enough : ipv4TailReceiveCount d (rest.drop (ipv4FirstCapacity d - 1)) ≤ 4096) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (suffixJson d p nodes (first :: rest)) ∧
        s.wg.device = some d ∧ s.wg.nlSock7 = socketReadbackFinal sock d) := by
  change Returns (wgGetDevice (byIndex d))
    (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
    (fun result g => result = .ok (suffixJson d p nodes (first :: rest)) ∧
      g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d)
  have caps := ipv4Pagination_capacity d room
  have positive := caps.1
  have fitting := caps.2.1
  have full := caps.2.2.1
  have size : (rest.take (ipv4FirstCapacity d - 1)).length = ipv4FirstCapacity d - 1 := by
    rw [List.length_take]
    simp only [List.length_cons] at many
    omega
  have decomposition := List.take_append_drop (ipv4FirstCapacity d - 1) rest
  cases remainder : rest.drop (ipv4FirstCapacity d - 1) with
  | nil =>
    have h := congrArg List.length remainder
    simp only [List.length_drop,List.length_nil,List.length_cons] at h many
    omega
  | cons start tail =>
    have listedSplit : p.allowedipsList = (first :: rest.take (ipv4FirstCapacity d - 1)) ++ start :: tail := by
      rw [listed,List.cons_append,← remainder,List.take_append_drop]
    have freshSplit : ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1)
        (first :: rest.take (ipv4FirstCapacity d - 1)) (start :: tail) := by
      simpa only [ipv4PaginationFresh,remainder] using fresh
    have readableSplit : Ipv4Residents d nodes
        ((first :: rest.take (ipv4FirstCapacity d - 1)) ++ start :: tail) := by
      simpa only [List.cons_append,← remainder,List.take_append_drop] using readable
    have result := wgGetDevice_ipv4_split_returns pid d p nodes
      (first :: rest.take (ipv4FirstCapacity d - 1)) start tail sock peers resident listedSplit
      (by simp) freshSplit readableSplit endpoint
      (by simp only [List.length_cons,size]; omega)
      (by simp only [List.length_cons,size]; omega) room idle empty
      (by simpa only [remainder] using enough)
    simpa only [List.cons_append,← remainder,List.take_append_drop] using result


end Leanux.Proofs.WG.Config
