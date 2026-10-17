import Leanux.Proofs.WG.Config.PaginationFirstSource
import Leanux.Proofs.WG.Config.PaginationStartSource
import Leanux.Proofs.WG.Config.PaginationCoalesceClaims
import Leanux.Proofs.WG.Config.PaginationChainSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original getter for any fitting IPv4 list, including the empty list.
The real first callback, DATA/DONE receives and coalescer are composed without
assuming a callback result. Both inline and separate DONE use at most two
receives of the original 4096-turn drain. -/
theorem wgGetDevice_ipv4_single_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids) (readable : Ipv4Residents d nodes ids)
    (endpoint : p.endpoint = none)
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fits : ids.length ≤ ipv4FirstCapacity d)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (wgGetDevice (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun result g => result = .ok (suffixJson d p nodes ids) ∧
        g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d) := by
  have finish (call : DumpCall) (part : PeerDumpAttrs)
      (completed : call.ret = 0) (cursor : call.ctx = {hasWg := true})
      (sequence : call.prevSeq = d.deviceUpdateGen)
      (data : call.skb.messages = [.data 2 (deviceFixedAttrs d) (some [part])])
      (callback : Returns (wgGetDeviceDump {hasWg := true} 0 {})
        (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some d))
      (coalesced : coalesce [.data 2 (deviceFixedAttrs d) (some [part]),.done 2 0] =
        pure (.ok (suffixJson d p nodes ids))) :
      Returns (wgGetDevice (byIndex d))
        (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
        (fun result g => result = .ok (suffixJson d p nodes ids) ∧
          g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d) := by
    let started : NlSock := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
    have drain := getterReceive_completed d started call part 0 4096 #[] rfl cursor sequence data
      (by split <;> decide)
    rw [wgGetDevice_source]
    refine returns_bind _ _ (netlinkDumpStart_completed_empty d sock call idle empty completed
      (by rw [cursor]) callback) ?_
    intro _ g ambient pre
    obtain ⟨value,final,after,run,valueEq,device,socket⟩ := drain g ambient pre
    simp only [Array.empty_append] at valueEq
    subst value
    refine ⟨.ok (suffixJson d p nodes ids),final,after,?_,rfl,device,?_⟩
    · rw [getterDrain_range_source]
      change (((forIn (List.range' 0 4096) (#[],false) receiveDumpStep).run g).run ambient >>= _) = _
      rw [run]
      change ((coalesce [.data 2 (deviceFixedAttrs d) (some [part]),.done 2 0]).run final).run after = _
      rw [coalesced]
      rfl
    · simpa [started,socketReadbackFinal] using socket
  cases ids with
  | nil =>
    let part : PeerDumpAttrs := {publicKey := hexKey p.remoteStatic,attrs := peerFixedAttrs p}
    let call := socketCallbackResult d {hasWg := true}
      (NLMSG_GOODSIZE - devicePrefixSpace d - peerFixedSpace p) part false
    apply finish call part rfl rfl rfl rfl
      (socketEmptyFirstCall_returns pid d p peers resident listed room)
    simpa [singlePeerDump,singlePeerJson,suffixJson,ipv4Jsons,part] using coalesce_single d p
  | cons a rest =>
    have enough : devicePrefixSpace d + 140 + 28 * (a :: rest).length ≤ NLMSG_GOODSIZE := by
      have capacity := (ipv4Pagination_capacity d room).2.1
      omega
    let part : PeerDumpAttrs := {socketFirstPeer p nodes (a :: rest) with split := false}
    let call := socketCallbackResult d {hasWg := true}
      (NLMSG_GOODSIZE - devicePrefixSpace d - (140 + 28 * (a :: rest).length)) part false
    apply finish call part rfl rfl rfl rfl
      (socketFirstCompleteCall_returns pid d p nodes a rest peers resident listed readable endpoint room enough)
    simpa [paginationMessages,paginationTailMessages,part] using
      coalesce_pagination d p nodes (a :: rest) [] endpoint

end Leanux.Proofs.WG.Config
