import Leanux.Proofs.WG.Config.PaginationBoundaryModel
import Leanux.Proofs.WG.Config.PaginationFinalSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem ipv4ResumeCall_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (before : List NodeId) (start : NodeId) (rest : List NodeId)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = before ++ start :: rest) (fresh : start ∉ before)
    (readable : Ipv4Residents d nodes (start :: rest))
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE) :
    Returns (wgGetDeviceDump
      {hasWg := true,nextAllowedip := some start,allowedipsSeq := d.peerAllowedips.seq}
      d.deviceUpdateGen {}) (fun g => g.dev = some d)
      (fun result g => result = ipv4ResumeCall d p nodes start rest ∧ g.dev = some d) := by
  have caps := ipv4Pagination_capacity d room
  have positive := caps.2.2.2.1
  have fits := caps.2.2.2.2.1
  have short := caps.2.2.2.2.2
  have decomposition := List.take_append_drop (ipv4ResumeCapacity d - 1) rest
  cases remainder : rest.drop (ipv4ResumeCapacity d - 1) with
  | nil =>
    have all : rest.take (ipv4ResumeCapacity d - 1) = rest := by
      simpa only [remainder,List.append_nil] using decomposition
    have size : rest.length ≤ ipv4ResumeCapacity d - 1 := by
      have h := congrArg List.length remainder
      simp only [List.length_drop,List.length_nil] at h
      omega
    have result := socketFinalCall_returns pid d p nodes before start rest peers resident
      listed fresh readable room (by simp only [List.length_cons]; omega)
    simpa only [ipv4ResumeCall,remainder,all] using result
  | cons next tail =>
    have size : (rest.take (ipv4ResumeCapacity d - 1)).length = ipv4ResumeCapacity d - 1 := by
      have h := congrArg List.length remainder
      simp only [List.length_drop,List.length_cons] at h
      rw [List.length_take]
      omega
    have selected : p.allowedipsList.dropWhile (· != start) =
        (start :: rest.take (ipv4ResumeCapacity d - 1)) ++ next :: tail := by
      rw [listed,cursor_after_prefix before start rest fresh]
      simpa only [remainder,List.cons_append] using congrArg (List.cons start) decomposition.symm
    have needed : Ipv4Residents d nodes
        ((start :: rest.take (ipv4ResumeCapacity d - 1)) ++ [next]) := by
      intro id member
      apply readable id
      have member' : id ∈ (start :: rest.take (ipv4ResumeCapacity d - 1)) ++ next :: tail := by
        simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
        rcases member with h | h
        · exact .inl h
        · exact .inr (.inl h)
      rw [← selected,listed,cursor_after_prefix before start rest fresh] at member'
      exact member'
    have result := socketResumeCall_returns pid d p nodes start
      (start :: rest.take (ipv4ResumeCapacity d - 1)) next tail peers resident selected
      (by simp) needed room
      (by simp only [List.length_cons,size]; omega)
      (by simp only [List.length_cons,size]; omega)
    simpa only [ipv4ResumeCall,remainder] using result


end Leanux.Proofs.WG.Config
