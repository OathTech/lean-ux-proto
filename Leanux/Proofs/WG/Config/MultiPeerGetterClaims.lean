import Leanux.Proofs.WG.Config.MultiPeerGetterModel
import Leanux.Proofs.WG.Config.MultiPeerGetterSource
import Leanux.Proofs.WG.Config.MultiPeerDumpSource
import Leanux.Proofs.WG.Config.MultiPeerCoalesceClaims
import Leanux.Proofs.WG.Config.PaginationStartSource
import Leanux.Proofs.WG.Config.ClaimView

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The actual getter returns a finite fitting peer list, preserving duplicates
and arbitrary endpoints. Residency, empty allowed-IP lists, the explicit buffer
bound and ordinary idle/empty selector state discharge all producer and receive
contracts; no reference, liveness or callback-success premise is supplied. -/
theorem fitting_peers_getter_returns (d : Device) (peers : PeerId → Peer) (sock : NlSock)
    (residents : ∀ pid ∈ d.peerList, d.peers[pid]? = some (peers pid))
    (emptyIps : ∀ pid ∈ d.peerList, (peers pid).allowedipsList = [])
    (room : devicePrefixSpace d + 168 * d.peerList.length + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (emptyQueue : sock.queue = []) :
    Campaign2.Returns (wgGetDevice (byIndex d))
      (fun s => s.wg.device = some d ∧ s.wg.nlSock7 = sock ∧ ClaimView.selectsDevice s d)
      (fun result s => result = .ok (multiPeerJson d peers) ∧ s.wg.device = some d ∧
        s.wg.nlSock7 = socketReadbackFinal sock d) := by
  let call := multiPeerCall d peers d.peerList
  let started : NlSock := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
  let current := paginationCompletedSocket started call
  let chunk : NlSkb := {call.skb with room := call.skb.room - nlmsgTotal 4,messages := call.skb.messages ++ [.done 2 0]}
  have enough : 20 ≤ call.skb.room := by
    have bound := multiPeerSpace_bound peers d.peerList
    change 20 ≤ NLMSG_GOODSIZE - devicePrefixSpace d - multiPeerSpace peers d.peerList
    omega
  have noSpill : ¬ call.skb.room < nlmsgTotal 4 := by change ¬ call.skb.room < 20; omega
  have start := netlinkDumpStart_completed_empty d sock call idle emptyQueue rfl rfl
    (wgGetDeviceDump_multi d peers residents emptyIps room)
  have coalesced : coalesce chunk.messages = pure (.ok (multiPeerJson d peers)) := by
    have nonempty : deviceFixedAttrs d ≠ [] := by simp [deviceFixedAttrs]
    cases memberList : d.peerList with
    | nil =>
      simp [chunk,call,multiPeerCall,memberList,multiPeerParts,multiPeerJson,coalesce,nonempty]
    | cons pid ids =>
      simpa [chunk,call,multiPeerCall,memberList,multiPeerJson] using
        coalesce_single_page d (multiPeerParts peers (pid :: ids))
  have drain := getterDrain_completed_page d current chunk
    (if d.peerList.isEmpty then none else some (multiPeerParts peers d.peerList))
    (multiPeerJson d peers) (by simp [current,paginationCompletedSocket,noSpill,started,chunk])
    (by simp [current,paginationCompletedSocket,noSpill]) rfl coalesced
  change Returns (wgGetDevice (byIndex d))
    (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
    (fun result g => result = .ok (multiPeerJson d peers) ∧ g.dev = some d ∧
      g.nlSock7 = socketReadbackFinal sock d)
  rw [wgGetDevice_source]
  apply returns_bind _ _ start
  intro value g ambient pre
  obtain ⟨result,final,after,run,resultEq,device,socket⟩ := drain g ambient pre
  refine ⟨result,final,after,run,resultEq,device,?_⟩
  change final.nlSock7 = _
  simp only [current,paginationCompletedSocket,noSpill,ite_false] at socket
  simpa [started,call,multiPeerCall,socketReadbackFinal] using socket


end Leanux.Proofs.WG.Config
