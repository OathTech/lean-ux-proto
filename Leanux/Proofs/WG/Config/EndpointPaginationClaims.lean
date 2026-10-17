import Leanux.Proofs.WG.Config.EndpointPaginationSource
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual finite IPv4 getter with arbitrary endpoint fields. Canonical
first boundaries account for the full endpoint attribute; later callbacks use
the unchanged resumed capacity. Count includes DATA and separate DONE, and all
callback/receive premises are discharged from the original source. -/
theorem endpointIpv4Pagination_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids) (fresh : endpointPaginationFresh d p ids)
    (readable : Ipv4Residents d nodes ids)
    (room : devicePrefixSpace d + max 168 (peerFixedSpace p + 32) ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (enough : endpointPaginationReceiveCount d p ids ≤ 4096) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (suffixJson d p nodes ids) ∧
        s.wg.device = some d ∧ s.wg.nlSock7 = socketReadbackFinal sock d) := by
  change Returns (wgGetDevice (byIndex d))
    (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
    (fun result g => result = .ok (suffixJson d p nodes ids) ∧
      g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d)
  cases ids with
  | nil =>
    exact wgGetDevice_endpoint_single_returns pid d p nodes [] sock peers resident listed readable
      room (Nat.zero_le _) idle empty
  | cons first rest =>
    by_cases fits : (first :: rest).length ≤ endpointFirstCapacity d p
    · exact wgGetDevice_endpoint_single_returns pid d p nodes (first :: rest) sock peers resident
        listed readable room fits idle empty
    · have caps := endpointFirstCapacity_bounds d p room
      have many : endpointFirstCapacity d p < (first :: rest).length := by omega
      have size : (rest.take (endpointFirstCapacity d p - 1)).length = endpointFirstCapacity d p - 1 := by
        rw [List.length_take]
        simp only [List.length_cons] at many
        omega
      have decomposition := List.take_append_drop (endpointFirstCapacity d p - 1) rest
      cases remainder : rest.drop (endpointFirstCapacity d p - 1) with
      | nil =>
        have h := congrArg List.length remainder
        simp only [List.length_drop,List.length_nil,List.length_cons] at h many
        omega
      | cons start tail =>
        have listedSplit : p.allowedipsList = (first :: rest.take (endpointFirstCapacity d p - 1)) ++ start :: tail := by
          rw [listed,List.cons_append,← remainder,List.take_append_drop]
        have freshSplit : ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1)
            (first :: rest.take (endpointFirstCapacity d p - 1)) (start :: tail) := by
          simpa only [endpointPaginationFresh,remainder] using fresh
        have readableSplit : Ipv4Residents d nodes
            ((first :: rest.take (endpointFirstCapacity d p - 1)) ++ start :: tail) := by
          simpa only [List.cons_append,← remainder,List.take_append_drop] using readable
        have result := wgGetDevice_endpoint_split_returns pid d p nodes
          (first :: rest.take (endpointFirstCapacity d p - 1)) start tail sock peers resident listedSplit
          (by simp) freshSplit readableSplit
          (by simp only [List.length_cons,size]; omega)
          (by simp only [List.length_cons,size]; omega) caps.1 idle empty
          (by simpa only [endpointPaginationReceiveCount,fits,ite_false,remainder] using enough)
        simpa only [List.cons_append,← remainder,List.take_append_drop] using result
end Leanux.Proofs.WG.Config
