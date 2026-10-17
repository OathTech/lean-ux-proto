import Leanux.Proofs.WG.Config.WeightedGetterModel
import Leanux.Proofs.WG.Config.WeightedReceiveSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Every resumed callback and receive is derived from the actual cursor,
readable suffix and all-prior boundary freshness. The receipt retains exact
socket states and the last DATA/DONE room decision. -/
theorem weightedTail_receipt (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (before : List NodeId) (start : NodeId) (rest : List NodeId)
    (sock : NlSock) (skb : NlSkb) (part : PeerDumpAttrs)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = before ++ start::rest)
    (readable : ∀ id ∈ start::rest, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fresh : weightedBoundaryFresh before
      (weightedTailPages nodes (NLMSG_GOODSIZE-devicePrefixSpace d-44) (start::rest)))
    (queued : sock.queue = [skb]) (running : sock.cbRunning = true)
    (active : 0 < sock.dumpDoneErrno)
    (cursor : sock.ctx = {hasWg := true,nextAllowedip := some start,allowedipsSeq := d.peerAllowedips.seq})
    (sequence : sock.prevSeq = d.deviceUpdateGen)
    (data : skb.messages = [.data 2 (deviceFixedAttrs d) (some [part])]) :
    WeightedReceiveReceipt d sock (socketReadbackFinal sock d)
      (.data 2 (deviceFixedAttrs d) (some [part]) ::
        jsonPaginationTailMessages d p
          ((weightedTailPages nodes (NLMSG_GOODSIZE-devicePrefixSpace d-44) (start::rest)).map
            (fun page => page.map (fun id => dumpNodeJson (nodes id)))))
      (1 + weightedTailReceives d nodes
        (weightedTailPages nodes (NLMSG_GOODSIZE-devicePrefixSpace d-44) (start::rest))) := by
  let room := NLMSG_GOODSIZE-devicePrefixSpace d-44
  have enough : 40 ≤ room := by dsimp [room]; omega
  have decomposition := weightedPrefix_spec nodes room (start::rest)
  have progress := weightedPrefix_progress nodes room start rest
    (Nat.le_trans (dumpNodeSpace_bounds _).2 enough)
  cases plan : weightedPrefix nodes room (start::rest) with
  | mk front remaining =>
    rw [plan] at decomposition progress
    dsimp only at decomposition progress
    have pages : weightedTailPages nodes room (start::rest) = front :: weightedTailPages nodes room remaining := by
      rw [weightedTailPages_prefix nodes room start rest enough,plan]
    change weightedBoundaryFresh before (weightedTailPages nodes room (start::rest)) at fresh
    rw [pages] at fresh
    cases front with
    | nil => exact False.elim (progress.1 rfl)
    | cons head tail =>
      have firstEq : head = start := by
        have original := decomposition.1
        simp only [List.cons_append,List.cons.injEq] at original
        exact original.1
      subst head
      have boundary : start ∉ before := fresh.1
      have callback := mixedResumeCall_returns pid d p nodes before start rest peers resident listed boundary readable header
      have actual : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {}) (fun g => g.dev = some d)
          (fun result g => result = mixedResumeCall d p nodes start rest ∧ g.dev = some d) := by
        simpa only [cursor,sequence] using callback
      cases remaining with
      | nil =>
        let call := mixedResumeCall d p nodes start rest
        let nextPart := {jsonSuffixPeer p ((start::tail).map (fun id => dumpNodeJson (nodes id))) with split := false}
        have completed : call.ret = 0 := by simp [call,mixedResumeCall,room,plan,socketCallbackResult]
        have callCursor : call.ctx = {hasWg := true} := by simp [call,mixedResumeCall,room,plan,socketCallbackResult]
        have callSequence : call.prevSeq = d.deviceUpdateGen := rfl
        have callData : call.skb.messages = [.data 2 (deviceFixedAttrs d) (some [nextPart])] := by
          simp [call,mixedResumeCall,room,plan,socketCallbackResult,nextPart,jsonSuffixPeer,dumpNodeJsons]
        have receiving := netlinkRecvmsg_completing d sock skb call queued running active completed
          (by rw [callCursor]) actual
        have done := weightedReceiveReceipt_completed d sock call nextPart running callCursor callSequence callData
        have receipt := weightedReceiveReceipt_prepend d sock (paginationCompletedSocket sock call)
          (socketReadbackFinal sock d) part _ _ (by simpa only [data] using receiving) done
        simpa [room,pages,weightedTailPages,weightedTailReceives,jsonPaginationTailMessages,
          call,mixedResumeCall,plan,socketCallbackResult,nextPart,Nat.add_comm] using receipt
      | cons next remaining =>
        have tailPages := weightedTailPages_prefix nodes room next remaining enough
        have morePages : (weightedTailPages nodes room (next::remaining)).isEmpty = false := by rw [tailPages]; rfl
        let call := mixedResumeCall d p nodes start rest
        let nextPart := {jsonSuffixPeer p ((start::tail).map (fun id => dumpNodeJson (nodes id))) with split := true}
        let nextSock := paginationMoreSocket sock call
        have callPositive : 0 < call.ret := by
          simp only [call,mixedResumeCall,room,plan,socketCallbackResult,List.isEmpty_cons,Bool.not_false,ite_true,Int.ofNat_eq_natCast,Int.natCast_pos]
          have prefixPositive : 0 < devicePrefixSpace d := by simp [devicePrefixSpace]; omega
          have fit := decomposition.2.1
          dsimp [room] at fit
          omega
        have callData : call.skb.messages = [.data 2 (deviceFixedAttrs d) (some [nextPart])] := by
          simp [call,mixedResumeCall,room,plan,socketCallbackResult,nextPart,jsonSuffixPeer,dumpNodeJsons]
        have receiving := netlinkRecvmsg_more d sock skb call queued running active callPositive actual
        have tailReceipt := weightedTail_receipt pid d p nodes (before ++ start::tail) next remaining
          nextSock call.skb nextPart peers resident
          (by rw [listed,← decomposition.1,List.append_assoc])
          (by intro id member; apply readable id; rw [← decomposition.1]; exact List.mem_append_right _ member)
          header fresh.2 rfl (by simpa [nextSock,paginationMoreSocket] using running)
          callPositive
          (by simp [nextSock,paginationMoreSocket,call,mixedResumeCall,room,plan,socketCallbackResult])
          rfl callData
        have receipt := weightedReceiveReceipt_prepend d sock nextSock (socketReadbackFinal nextSock d)
          part _ _ (by simpa only [data] using receiving) tailReceipt
        simpa [room,pages,weightedTailReceives,morePages,jsonPaginationTailMessages,
          nextSock,paginationMoreSocket,socketReadbackFinal,nextPart,Nat.add_assoc,Nat.add_comm] using receipt
termination_by rest.length + 1
decreasing_by
  simp_wf
  have smaller := progress.2
  simp only [List.length_cons] at smaller
  omega

end Leanux.Proofs.WG.Config
