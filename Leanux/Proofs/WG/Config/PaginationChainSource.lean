import Leanux.Proofs.WG.Config.PaginationCanonicalSource
import Leanux.Proofs.WG.Config.PaginationCompletionSource
import Leanux.Proofs.WG.Config.PaginationCoalesceClaims

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- Every resumed callback and receive of the original drain, on the exact
canonical boundaries. Freshness is against the entire previously emitted
prefix; no individual callback execution is supplied as a premise. -/
theorem ipv4ResumeDrain_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (before : List NodeId) (start : NodeId) (rest : List NodeId)
    (sock : NlSock) (skb : NlSkb) (part : PeerDumpAttrs)
    (step budget : Nat) (messages : Array NlMessage)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = before ++ start :: rest)
    (fresh : ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1) before (start :: rest))
    (readable : Ipv4Residents d nodes (start :: rest))
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (queued : sock.queue = [skb]) (data : skb.messages = [.data 2 (deviceFixedAttrs d) (some [part])])
    (running : sock.cbRunning = true) (active : 0 < sock.dumpDoneErrno)
    (cursor : sock.ctx = {hasWg := true,nextAllowedip := some start,allowedipsSeq := d.peerAllowedips.seq})
    (sequence : sock.prevSeq = d.deviceUpdateGen)
    (enough : ipv4TailReceiveCount d (start :: rest) ≤ budget) :
    Returns (forIn (List.range' step budget) (messages,false) receiveDumpStep)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result =
        (messages ++ (NlMessage.data 2 (deviceFixedAttrs d) (some [part]) ::
          paginationTailMessages d p nodes (ipv4TailPages (ipv4ResumeCapacity d - 1) (start :: rest))).toArray,true) ∧
        g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d) := by
  have freshParts : start ∉ before ∧
      ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1)
        (before ++ start :: rest.take (ipv4ResumeCapacity d - 1))
        (rest.drop (ipv4ResumeCapacity d - 1)) := by
    simpa only [ipv4TailBoundaryFresh] using fresh
  have callback := ipv4ResumeCall_returns pid d p nodes before start rest peers resident
    listed freshParts.1 readable room
  have actualCallback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun g => g.dev = some d)
      (fun result g => result = ipv4ResumeCall d p nodes start rest ∧ g.dev = some d) := by
    simpa only [cursor,sequence] using callback
  have decomposition := List.take_append_drop (ipv4ResumeCapacity d - 1) rest
  cases remainder : rest.drop (ipv4ResumeCapacity d - 1) with
  | nil =>
    have all : rest.take (ipv4ResumeCapacity d - 1) = rest := by
      simpa only [remainder,List.append_nil] using decomposition
    have exactCall : ipv4ResumeCall d p nodes start rest = socketLastCall d p nodes (start :: rest) := by
      simp only [ipv4ResumeCall,remainder,all]
    have receiving := netlinkRecvmsg_completing d sock skb (socketLastCall d p nodes (start :: rest))
      queued running active rfl rfl (by simpa only [exactCall] using actualCallback)
    have first := receiveDumpStep_data d sock
      (paginationCompletedSocket sock (socketLastCall d p nodes (start :: rest)))
      step messages 2 (deviceFixedAttrs d) (some [part]) (by simpa only [data] using receiving)
    have budgetPositive : 0 < budget := by
      simp only [ipv4TailReceiveCount,remainder,List.length_cons] at enough
      split at enough <;> omega
    cases budget with
    | zero => omega
    | succ budget =>
      have tailRun := getterReceive_completed d sock (socketLastCall d p nodes (start :: rest))
        (suffixLast p nodes (start :: rest)) (step+1) budget
        (messages.push (.data 2 (deviceFixedAttrs d) (some [part]))) running rfl rfl rfl
        (by
          change (if NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + 28 * (start :: rest).length) < 20 then 2 else 1) ≤ budget
          rw [ipv4TailReceiveCount,remainder] at enough
          change (if NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + 28 * (start :: rest).length) < 20 then 3 else 2) ≤ budget + 1 at enough
          by_cases h : NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + 28 * (start :: rest).length) < 20
          · simp only [h,ite_true] at enough ⊢; omega
          · simp only [h,ite_false] at enough ⊢; omega)
      intro g ambient pre
      obtain ⟨value,middle,midAmbient,run,valueEq,midDevice,midSocket⟩ := first g ambient pre
      subst value
      obtain ⟨result,final,after,restRun,resultEq,finalDevice,finalSocket⟩ :=
        tailRun middle midAmbient ⟨midDevice,midSocket⟩
      refine ⟨result,final,after,?_,?_,finalDevice,finalSocket⟩
      · rw [List.range'_succ,List.forIn_cons]
        change (((receiveDumpStep step (messages,false)).run g).run ambient >>= _) = _
        rw [run]
        exact restRun
      · rw [ipv4TailPages,remainder,all,ipv4TailPages]
        simp only [paginationTailMessages,List.isEmpty_nil]
        rw [List.toArray_cons]
        rw [← Array.append_assoc]
        exact resultEq
  | cons next tail =>
    let call := ipv4ResumeCall d p nodes start rest
    let nextSock := paginationMoreSocket sock call
    let front := start :: rest.take (ipv4ResumeCapacity d - 1)
    have callPositive : 0 < call.ret := by
      simp only [call,ipv4ResumeCall,remainder,socketCallbackResult,ite_true]
      apply Int.natCast_pos.mpr
      unfold NLMSG_GOODSIZE
      omega
    have receiving := netlinkRecvmsg_more d sock skb call queued running active callPositive actualCallback
    have first := receiveDumpStep_data d sock nextSock step messages
      2 (deviceFixedAttrs d) (some [part]) (by simpa only [data] using receiving)
    have nextListed : p.allowedipsList = (before ++ front) ++ next :: tail := by
      rw [listed,List.append_assoc]
      dsimp only [front]
      rw [List.cons_append,← remainder,List.take_append_drop]
    have nextFresh : ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1)
        (before ++ front) (next :: tail) := by
      simpa only [front,remainder] using freshParts.2
    have nextReadable : Ipv4Residents d nodes (next :: tail) := by
      intro id member
      apply readable id
      exact List.mem_cons_of_mem start (List.mem_of_mem_drop (remainder ▸ member))
    have budgetPositive : 0 < budget := by
      simp only [ipv4TailReceiveCount,remainder] at enough
      omega
    cases budget with
    | zero => omega
    | succ budget =>
      have tailRun := ipv4ResumeDrain_returns pid d p nodes (before ++ front) next tail
        nextSock call.skb {suffixLast p nodes front with split := true}
        (step+1) budget (messages.push (.data 2 (deviceFixedAttrs d) (some [part])))
        peers resident nextListed nextFresh nextReadable room rfl
        (by simp [call,ipv4ResumeCall,remainder,socketCallbackResult,front])
        (by simpa [nextSock,paginationMoreSocket] using running)
        (by simpa [nextSock,paginationMoreSocket] using callPositive)
        (by simp [nextSock,paginationMoreSocket,call,ipv4ResumeCall,remainder,socketCallbackResult])
        (by simp [nextSock,paginationMoreSocket,call,ipv4ResumeCall,remainder,socketCallbackResult])
        (by
          rw [ipv4TailReceiveCount,remainder] at enough
          change 1 + ipv4TailReceiveCount d (next :: tail) ≤ budget + 1 at enough
          omega)
      intro g ambient pre
      obtain ⟨value,middle,midAmbient,run,valueEq,midDevice,midSocket⟩ := first g ambient pre
      subst value
      obtain ⟨result,final,after,restRun,resultEq,finalDevice,finalSocket⟩ :=
        tailRun middle midAmbient ⟨midDevice,midSocket⟩
      refine ⟨result,final,after,?_,?_,finalDevice,?_⟩
      · rw [List.range'_succ,List.forIn_cons]
        change (((receiveDumpStep step (messages,false)).run g).run ambient >>= _) = _
        rw [run]
        exact restRun
      · have nonempty : (ipv4TailPages (ipv4ResumeCapacity d - 1) (next :: tail)).isEmpty = false := by
          rw [ipv4TailPages]; rfl
        rw [ipv4TailPages,remainder,paginationTailMessages,nonempty]
        change result = (messages ++ (NlMessage.data 2 (deviceFixedAttrs d) (some [part]) ::
          NlMessage.data 2 (deviceFixedAttrs d) (some [{suffixLast p nodes front with split := true}]) ::
          paginationTailMessages d p nodes (ipv4TailPages (ipv4ResumeCapacity d - 1) (next :: tail))).toArray,true)
        rw [List.toArray_cons,← Array.append_assoc]
        exact resultEq
      · simpa [socketReadbackFinal,nextSock,paginationMoreSocket] using finalSocket
termination_by rest.length
decreasing_by
  have h := congrArg List.length remainder
  simp only [List.length_drop,List.length_cons] at h
  omega

/-- The unchanged drain expressed with the list loop used by its checked
finite-receive contracts. Factoring through the existing first-step equation
avoids reducing the concrete 4096-element range in a later source proof. -/
theorem getterDrain_range_source :
    getterDrainSource = (do
      let (messages,finished) ← forIn (List.range' 0 4096) (#[],false) receiveDumpStep
      if !finished then invariant "op 9: the dump did not finish"
      coalesce messages.toList) := by
  rw [getterDrain_first]
  conv => rhs; rw [show 4096 = 4095 + 1 from rfl,List.range'_succ,List.forIn_cons]
  simp only [bind_assoc]
  congr 1
  funext first
  cases first <;> simp

/-- Original getter drain from its real first split callback. Every later
callback is derived from canonical page capacity and actual cursor lookup. -/
theorem getterDrain_ipv4_split_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (front : List NodeId) (start : NodeId) (rest : List NodeId)
    (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = front ++ start :: rest)
    (fresh : ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1) front (start :: rest))
    (readable : Ipv4Residents d nodes (start :: rest)) (endpoint : p.endpoint = none)
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE) (empty : sock.queue = [])
    (enough : ipv4TailReceiveCount d (start :: rest) ≤ 4096) :
    Returns getterDrainSource
      (fun g => g.dev = some d ∧ g.nlSock7 = socketFirstState sock d p nodes front start)
      (fun result g => result = .ok (suffixJson d p nodes (front ++ start :: rest)) ∧
        g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d) := by
  have drain := ipv4ResumeDrain_returns pid d p nodes front start rest
    (socketFirstState sock d p nodes front start) (socketFirstCall d p nodes front start).skb
    (socketFirstPeer p nodes front) 0 4096 #[] peers resident listed fresh readable room
    (by simp [socketFirstState,empty]) rfl rfl (socketFirstCall_positive d p nodes front start)
    rfl rfl enough
  have nonempty : (ipv4TailPages (ipv4ResumeCapacity d - 1) (start :: rest)).isEmpty = false := by
    rw [ipv4TailPages]; rfl
  have messageEq : NlMessage.data 2 (deviceFixedAttrs d) (some [socketFirstPeer p nodes front]) ::
      paginationTailMessages d p nodes (ipv4TailPages (ipv4ResumeCapacity d - 1) (start :: rest)) =
      paginationMessages d p nodes front (ipv4TailPages (ipv4ResumeCapacity d - 1) (start :: rest)) := by
    rw [paginationMessages,nonempty]
    rfl
  intro g ambient pre
  obtain ⟨result,final,after,run,resultEq,device,socket⟩ := drain g ambient pre
  simp only [Array.empty_append,messageEq] at resultEq
  subst result
  refine ⟨.ok (suffixJson d p nodes (front ++ start :: rest)),final,after,?_,rfl,device,?_⟩
  · rw [getterDrain_range_source]
    change (((forIn (List.range' 0 4096) (#[],false) receiveDumpStep).run g).run ambient >>= _) = _
    rw [run]
    change ((coalesce ((paginationMessages d p nodes front
      (ipv4TailPages (ipv4ResumeCapacity d - 1) (start :: rest))).toArray.toList)).run final).run after = _
    rw [List.toList_toArray,coalesce_pagination d p nodes front _ endpoint,ipv4TailPages_flatten]
    rfl
  · simpa [socketReadbackFinal,socketFirstState] using socket

/-- Whole actual getter for a first split page and any number of subsequent
canonical IPv4 pages. No callback or receive outcome is assumed. -/
theorem wgGetDevice_ipv4_split_returns (pid : PeerId) (d : Device) (p : Peer)
    (nodes : NodeId → AipNode) (front : List NodeId) (start : NodeId) (rest : List NodeId)
    (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (listed : p.allowedipsList = front ++ start :: rest) (nonempty : front ≠ [])
    (fresh : ipv4TailBoundaryFresh (ipv4ResumeCapacity d - 1) front (start :: rest))
    (readable : Ipv4Residents d nodes (front ++ start :: rest)) (endpoint : p.endpoint = none)
    (fits : devicePrefixSpace d + 140 + 28 * front.length ≤ NLMSG_GOODSIZE)
    (short : NLMSG_GOODSIZE < devicePrefixSpace d + 140 + 28 * (front.length+1))
    (room : devicePrefixSpace d + 168 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (enough : ipv4TailReceiveCount d (start :: rest) ≤ 4096) :
    Returns (wgGetDevice (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun result g => result = .ok (suffixJson d p nodes (front ++ start :: rest)) ∧
        g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d) := by
  have firstNodes : Ipv4Residents d nodes (front ++ [start]) := by
    intro id member
    apply readable id
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member ⊢
    rcases member with h | h
    · exact .inl h
    · exact .inr (.inl h)
  have remaining : Ipv4Residents d nodes (start :: rest) := by
    intro id member
    exact readable id (List.mem_append_right front member)
  have first := socketFirstCall_returns pid d p nodes front start rest peers resident
    listed nonempty firstNodes endpoint fits short
  rw [wgGetDevice_source]
  exact returns_bind _ _ (netlinkDumpStart_front d p nodes front start sock idle first)
    (fun _ => getterDrain_ipv4_split_returns pid d p nodes front start rest sock peers resident
      listed fresh remaining endpoint room empty enough)


end Leanux.Proofs.WG.Config
