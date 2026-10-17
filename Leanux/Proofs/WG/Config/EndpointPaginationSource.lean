import Leanux.Proofs.WG.Config.EndpointPaginationFirstSource
import Leanux.Proofs.WG.Config.EndpointPaginationCoalesceClaims
import Leanux.Proofs.WG.Config.EndpointPaginationTransportSource
import Leanux.Proofs.WG.Config.DumpCoalesce

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The existing finite resumed-page induction starts from the actual
endpoint-aware first DATA envelope; every later callback is derived. -/
theorem wgGetDevice_endpoint_split_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (front : List NodeId) (start : NodeId) (rest : List NodeId)
    (sock : NlSock) (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = front ++ start :: rest) (nonempty : front ≠ [])
    (fresh : ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1) front (start :: rest))
    (readable : Ipv4Residents d nodes (front ++ start :: rest))
    (fits : devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * front.length ≤ NLMSG_GOODSIZE)
    (short : NLMSG_GOODSIZE < devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * (front.length+1))
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (enough : ipv4TailReceiveCount d (start :: rest) ≤ 4096) :
    Returns (wgGetDevice (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun result g => result = .ok (suffixJson d p nodes (front ++ start :: rest)) ∧
        g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d) := by
  let call := endpointFirstCall d p nodes front start
  let started : NlSock := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
  have positive : 0 < call.ret := by
    simp only [call,endpointFirstCall,socketCallbackResult,ite_true]
    apply Int.natCast_pos.mpr
    unfold NLMSG_GOODSIZE
    omega
  have firstNodes : Ipv4Residents d nodes (front ++ [start]) := by
    intro id member
    apply readable id
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
    rcases member with h | h
    · exact .inl h
    · exact .inr (.inl h)
  have remaining : Ipv4Residents d nodes (start :: rest) := fun id member =>
    readable id (List.mem_append_right front member)
  have first := endpointFirstSplit_returns pid d p nodes front start rest peers resident listed nonempty
    firstNodes room fits short
  have drain := ipv4ResumeDrain_returns pid d p nodes front start rest
    (paginationMoreSocket started call) call.skb (socketFirstPeer p nodes front) 0 4096 #[]
    peers resident listed fresh remaining room rfl rfl rfl positive rfl rfl enough
  have pagesNonempty : (ipv4TailPages (ipv4ResumeCapacity d - 1) (start :: rest)).isEmpty = false := by
    rw [ipv4TailPages]; rfl
  have messageEq : NlMessage.data 2 (deviceFixedAttrs d) (some [socketFirstPeer p nodes front]) ::
      paginationTailMessages d p nodes (ipv4TailPages (ipv4ResumeCapacity d - 1) (start :: rest)) =
      paginationMessages d p nodes front (ipv4TailPages (ipv4ResumeCapacity d - 1) (start :: rest)) := by
    rw [paginationMessages,pagesNonempty]
    rfl
  rw [wgGetDevice_source]
  refine returns_bind _ _ (netlinkDumpStart_more_empty d sock call idle empty positive first) ?_
  intro _ g ambient pre
  obtain ⟨result,final,after,run,resultEq,device,socket⟩ := drain g ambient pre
  simp only [Array.empty_append,messageEq] at resultEq
  subst result
  refine ⟨.ok (suffixJson d p nodes (front ++ start :: rest)),final,after,?_,rfl,device,?_⟩
  · rw [getterDrain_range_source]
    change (((forIn (List.range' 0 4096) (#[],false) receiveDumpStep).run g).run ambient >>= _) = _
    rw [run]
    change ((coalesce ((paginationMessages d p nodes front
      (ipv4TailPages (ipv4ResumeCapacity d - 1) (start :: rest))).toArray.toList)).run final).run after = _
    rw [List.toList_toArray,coalesce_pagination_endpoint,ipv4TailPages_flatten]
    rfl
  · simpa [socketReadbackFinal,paginationMoreSocket,started] using socket

/-- Whole actual getter when all IPv4 entries fit the endpoint-aware first
page, including the empty-list case and the real DONE spill branch. -/
theorem wgGetDevice_endpoint_single_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids) (readable : Ipv4Residents d nodes ids)
    (room : devicePrefixSpace d + max 168 (peerFixedSpace p + 32) ≤ NLMSG_GOODSIZE)
    (fits : ids.length ≤ endpointFirstCapacity d p)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (wgGetDevice (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun result g => result = .ok (suffixJson d p nodes ids) ∧
        g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d) := by
  have caps := endpointFirstCapacity_bounds d p room
  cases ids with
  | nil =>
    let part : PeerDumpAttrs := {publicKey := hexKey p.remoteStatic,attrs := peerFixedAttrs p}
    let call := socketCallbackResult d {hasWg := true}
      (NLMSG_GOODSIZE - devicePrefixSpace d - peerFixedSpace p) part false
    apply getter_completed_callback_returns d sock call part (suffixJson d p nodes []) idle empty rfl rfl rfl rfl
      (socketEmptyFirstCall_returns pid d p peers resident listed caps.1)
    simpa [singlePeerDump,singlePeerJson,suffixJson,ipv4Jsons,part] using coalesce_single d p
  | cons first rest =>
    have enough : devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * (first :: rest).length ≤ NLMSG_GOODSIZE := by omega
    let part : PeerDumpAttrs := {socketFirstPeer p nodes (first :: rest) with split := false}
    let call := socketCallbackResult d {hasWg := true}
      (NLMSG_GOODSIZE - (devicePrefixSpace d + (peerFixedSpace p + 4) + 28 * (first :: rest).length)) part false
    apply getter_completed_callback_returns d sock call part (suffixJson d p nodes (first :: rest)) idle empty
      rfl rfl rfl rfl
      (endpointFirstComplete_returns pid d p nodes first rest peers resident listed readable caps.1 enough)
    simpa [paginationMessages,paginationTailMessages,part] using
      coalesce_pagination_endpoint d p nodes (first :: rest) []
end Leanux.Proofs.WG.Config
