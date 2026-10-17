import Leanux.Proofs.WG.Config.WeightedTailSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Derive the complete actual receive family from the first callback. No
successful callback or receive execution is an input premise. -/
theorem weightedGetter_receipt (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (fresh : weightedGetterFresh d p nodes ids) :
    WeightedReceiveReceipt d (mixedStartedSocket sock (mixedFirstCall d p nodes ids))
      (socketReadbackFinal sock d) (weightedGetterMessages d p nodes ids)
      (weightedGetterReceives d p nodes ids) := by
  let started : NlSock := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
  cases ids with
  | nil =>
    have receipt := weightedReceiveReceipt_completed d started (mixedFirstCall d p nodes [])
      {publicKey := hexKey p.remoteStatic,attrs := peerFixedAttrs p} rfl rfl rfl rfl
    simpa [weightedGetterMessages,weightedGetterReceives,weightedPrefix,mixedStartedSocket,
      mixedFirstCall,socketCallbackResult,started,socketReadbackFinal] using receipt
  | cons first rest =>
    let firstRoom := NLMSG_GOODSIZE-devicePrefixSpace d-(peerFixedSpace p+4)
    let resumeRoom := NLMSG_GOODSIZE-devicePrefixSpace d-44
    have decomposition := weightedPrefix_spec nodes firstRoom (first::rest)
    cases plan : weightedPrefix nodes firstRoom (first::rest) with
    | mk front remaining =>
      rw [plan] at decomposition
      dsimp only at decomposition
      change weightedBoundaryFresh (weightedPrefix nodes firstRoom (first::rest)).1
        (weightedTailPages nodes resumeRoom (weightedPrefix nodes firstRoom (first::rest)).2) at fresh
      rw [plan] at fresh
      cases remaining with
      | nil =>
        let call := mixedFirstCall d p nodes (first::rest)
        let part := {jsonFirstPeer p (front.map (fun id => dumpNodeJson (nodes id))) with split := false}
        have completed : call.ret = 0 := by simp [call,mixedFirstCall,firstRoom,plan,socketCallbackResult]
        have cursor : call.ctx = {hasWg := true} := by simp [call,mixedFirstCall,firstRoom,plan,socketCallbackResult]
        have data : call.skb.messages = [.data 2 (deviceFixedAttrs d) (some [part])] := by
          simp [call,mixedFirstCall,firstRoom,plan,socketCallbackResult,part,jsonFirstPeer,dumpNodeJsons]
        have receipt := weightedReceiveReceipt_completed d started call part rfl cursor rfl data
        simpa [weightedGetterMessages,weightedGetterReceives,mixedStartedSocket,completed,
          firstRoom,plan,weightedTailPages,jsonPaginationMessages,jsonPaginationTailMessages,
          call,part,started,socketReadbackFinal] using receipt
      | cons next remaining =>
        let call := mixedFirstCall d p nodes (first::rest)
        let part := jsonFirstPeer p (front.map (fun id => dumpNodeJson (nodes id)))
        have positive : 0 < call.ret := by
          simp only [call,mixedFirstCall,firstRoom,plan,socketCallbackResult,
            List.isEmpty_cons,Bool.not_false,ite_true,Int.ofNat_eq_natCast,Int.natCast_pos]
          have prefixPositive : 0 < devicePrefixSpace d := by simp [devicePrefixSpace]; omega
          omega
        have nonzero : call.ret ≠ 0 := by omega
        have data : call.skb.messages = [.data 2 (deviceFixedAttrs d) (some [part])] := by
          simp [call,mixedFirstCall,firstRoom,plan,socketCallbackResult,part,jsonFirstPeer,dumpNodeJsons]
        have receipt := weightedTail_receipt pid d p nodes front next remaining
          (paginationMoreSocket started call) call.skb part peers resident
          (by rw [listed,decomposition.1])
          (by intro id member; apply readable id; rw [← decomposition.1]; exact List.mem_append_right _ member)
          header fresh rfl rfl positive
          (by simp [paginationMoreSocket,call,mixedFirstCall,firstRoom,plan,socketCallbackResult]) rfl data
        have pagesNonempty : (weightedTailPages nodes resumeRoom (next::remaining)).isEmpty = false := by
          rw [weightedTailPages_prefix nodes resumeRoom next remaining (by dsimp [resumeRoom]; omega)]
          rfl
        simpa [weightedGetterMessages,weightedGetterReceives,mixedStartedSocket,nonzero,
          firstRoom,plan,jsonPaginationMessages,pagesNonempty,resumeRoom,
          call,part,jsonFirstPeer,started,socketReadbackFinal,paginationMoreSocket] using receipt

/-- Coalescing the derived raw pages returns every original list occurrence
in order, using the original stored-width mask/hex serializer. -/
theorem weightedGetter_coalesce (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE) :
    coalesce (weightedGetterMessages d p nodes ids) =
      pure (.ok (jsonPaginationResult d p (ids.map (fun id => dumpNodeJson (nodes id))))) := by
  cases ids with
  | nil => simpa [weightedGetterMessages,singlePeerDump,singlePeerJson,jsonPaginationResult]
      using coalesce_single d p
  | cons first rest =>
    let result := weightedPrefix nodes (NLMSG_GOODSIZE-devicePrefixSpace d-(peerFixedSpace p+4)) (first::rest)
    have decomposition := (weightedPrefix_spec nodes
      (NLMSG_GOODSIZE-devicePrefixSpace d-(peerFixedSpace p+4)) (first::rest)).1
    have flattened := (weightedTailPages_spec nodes (NLMSG_GOODSIZE-devicePrefixSpace d-44)
      (by omega) result.2).1
    have combined : result.1 ++ (weightedTailPages nodes
        (NLMSG_GOODSIZE-devicePrefixSpace d-44) result.2).flatten = first::rest := by
      rw [flattened]; exact decomposition
    unfold weightedGetterMessages
    rw [coalesce_json_pagination]
    congr 3
    simpa only [List.map_append,List.map_flatten,List.map_map] using
      congrArg (List.map (fun id => dumpNodeJson (nodes id))) combined

/-- Whole original getter, using the generic finite receive-loop theorem.
The sole count premise is the exact DATA-plus-possible-DONE envelope count. -/
theorem weightedGetter_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (ids : List NodeId) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = ids)
    (readable : ∀ id ∈ ids, d.nodes[id]? = some (nodes id))
    (header : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (nest : ids ≠ [] → devicePrefixSpace d + (peerFixedSpace p+4) ≤ NLMSG_GOODSIZE)
    (fresh : weightedGetterFresh d p nodes ids)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (within : weightedGetterReceives d p nodes ids ≤ 4096) :
    Returns (wgGetDevice (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun result g => result = .ok (jsonPaginationResult d p
        (ids.map (fun id => dumpNodeJson (nodes id)))) ∧ g.dev = some d ∧
        g.nlSock7 = socketReadbackFinal sock d) := by
  have receipt := weightedGetter_receipt pid d p nodes ids sock peers resident listed readable header fresh
  have drain := weightedReceiveReceipt_run d _ _ _ _ 4096 receipt within
  rw [wgGetDevice_source]
  refine returns_bind _ _ (netlinkDumpStart_mixed_returns pid d p nodes ids sock
    peers resident listed readable header nest idle empty) ?_
  intro _ g ambient pre
  obtain ⟨value,final,after,run,valueEq,device,socket⟩ := drain g ambient pre
  subst value
  refine ⟨_,final,after,?_,rfl,device,socket⟩
  rw [getterDrain_range_source]
  change (((forIn (List.range' 0 4096) (#[],false) receiveDumpStep).run g).run ambient >>= _) = _
  rw [run]
  change ((coalesce (weightedGetterMessages d p nodes ids)).run final).run after = _
  rw [weightedGetter_coalesce d p nodes ids header]
  rfl

end Leanux.Proofs.WG.Config
