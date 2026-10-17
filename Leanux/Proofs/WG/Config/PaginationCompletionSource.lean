import Leanux.Proofs.WG.Config.PaginationBoundaryModel
import Leanux.Proofs.WG.Config.PaginationReceiveSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem netlinkRecvmsg_completing (d : Device) (sock : NlSock) (skb : NlSkb) (call : DumpCall)
    (queued : sock.queue = [skb]) (running : sock.cbRunning = true)
    (active : 0 < sock.dumpDoneErrno) (completed : call.ret = 0)
    (cursor : call.ctx.nextPeer = none)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some d)) :
    Returns (netlinkRecvmsg 7) (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some skb.messages ∧ g.dev = some d ∧
        g.nlSock7 = paginationCompletedSocket sock call) := by
  intro g ambient pre
  let popped : NlSock := {sock with queue := []}
  let current : WGWorld := {g with nlSock7 := popped}
  by_cases spill : call.skb.room < nlmsgTotal 4
  · obtain ⟨value,final,after,run,finalDevice,finalSocket⟩ :=
      netlinkDump_completed_spill d popped call active completed spill callback
        current ambient ⟨pre.1,rfl⟩
    cases value
    refine ⟨some skb.messages,final,after,?_,rfl,finalDevice,?_⟩
    · simp [netlinkRecvmsg,getNlSock,pre.2,queued,setNlSock,running]
      simp only [current,popped,running] at run
      rw [run]
      rfl
    · simpa [popped,paginationCompletedSocket,spill] using finalSocket
  · obtain ⟨value,final,after,run,finalDevice,finalSocket⟩ :=
      netlinkDump_completed_fits d popped call active completed (by omega) cursor callback
        current ambient ⟨pre.1,rfl⟩
    cases value
    refine ⟨some skb.messages,final,after,?_,rfl,finalDevice,?_⟩
    · simp [netlinkRecvmsg,getNlSock,pre.2,queued,setNlSock,running]
      simp only [current,popped,running] at run
      rw [run]
      rfl
    · simpa [popped,paginationCompletedSocket,spill] using finalSocket

theorem netlinkRecvmsg_quiescent (device : Option Device) (sock : NlSock) (skb : NlSkb)
    (queued : sock.queue = [skb]) (quiet : sock.cbRunning = false) :
    Returns (netlinkRecvmsg 7) (fun g => g.dev = device ∧ g.nlSock7 = sock)
      (fun result g => result = some skb.messages ∧ g.dev = device ∧
        g.nlSock7 = {sock with queue := []}) := by
  intro g ambient pre
  refine ⟨some skb.messages,{g with nlSock7 := {sock with queue := []}},ambient,?_,rfl,pre.1,rfl⟩
  simp [netlinkRecvmsg,getNlSock,pre.2,queued,setNlSock,quiet]
  rfl

theorem receiveDumpStep_finishing (d : Device) (sock nextSock : NlSock)
    (step : Nat) (messages : Array NlMessage) (part : Option PeerDumpAttrs)
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some
        ((part.toList.map fun p => NlMessage.data 2 (deviceFixedAttrs d) (some [p])) ++ [NlMessage.done 2 0]) ∧
        g.dev = some d ∧ g.nlSock7 = nextSock)) :
    Returns (receiveDumpStep step (messages,false))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = .yield
        (messages ++ ((part.toList.map fun p => NlMessage.data 2 (deviceFixedAttrs d) (some [p])) ++
          [NlMessage.done 2 0]).toArray,true) ∧ g.dev = some d ∧ g.nlSock7 = nextSock) := by
  simp only [receiveDumpStep,Bool.false_eq_true,ite_false]
  apply returns_bind _ _ receive
  intro result g ambient pre
  obtain ⟨rfl,device,socket⟩ := pre
  refine ⟨_,g,ambient,?_,rfl,device,socket⟩
  cases part <;> simp [List.forIn_cons,List.forIn_nil]
  all_goals simp only [Array.push_eq_append,Array.append_assoc]; rfl

/-- Terminal inline DONE is one real receive and then the original loop's
finished branch, irrespective of how much receive budget remains. -/
theorem getterReceive_finishing (d : Device) (sock nextSock : NlSock)
    (step budget : Nat) (messages : Array NlMessage) (part : Option PeerDumpAttrs)
    (positive : 0 < budget)
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some
        ((part.toList.map fun p => NlMessage.data 2 (deviceFixedAttrs d) (some [p])) ++
          [NlMessage.done 2 0]) ∧ g.dev = some d ∧ g.nlSock7 = nextSock)) :
    Returns (forIn (List.range' step budget) (messages,false) receiveDumpStep)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result =
        (messages ++ ((part.toList.map fun p => NlMessage.data 2 (deviceFixedAttrs d) (some [p])) ++
          [NlMessage.done 2 0]).toArray,true) ∧ g.dev = some d ∧ g.nlSock7 = nextSock) := by
  cases budget with
  | zero => omega
  | succ budget =>
    intro g ambient pre
    obtain ⟨result,final,after,run,value,device,socket⟩ :=
      receiveDumpStep_finishing d sock nextSock step messages part receive g ambient pre
    subst result
    refine ⟨_,final,after,?_,rfl,device,socket⟩
    rw [List.range'_succ,List.forIn_cons]
    change (((receiveDumpStep step (messages,false)).run g).run ambient >>= _) = _
    rw [run]
    change ((forIn (List.range' (step+1) budget) (_,true) receiveDumpStep).run final).run after = _
    rw [receiveDump_finished]
    rfl

/-- Complete a queued final DATA exactly, taking one receive if DONE is inline
and two when the actual room test requires a separate DONE envelope. -/
theorem getterReceive_completed (d : Device) (sock : NlSock) (call : DumpCall)
    (part : PeerDumpAttrs) (step budget : Nat) (messages : Array NlMessage)
    (running : sock.cbRunning = true) (cursor : call.ctx = {hasWg := true})
    (sequence : call.prevSeq = d.deviceUpdateGen)
    (data : call.skb.messages = [.data 2 (deviceFixedAttrs d) (some [part])])
    (enough : (if call.skb.room < nlmsgTotal 4 then 2 else 1) ≤ budget) :
    Returns (forIn (List.range' step budget) (messages,false) receiveDumpStep)
      (fun g => g.dev = some d ∧ g.nlSock7 = paginationCompletedSocket sock call)
      (fun result g => result =
        (messages ++ #[NlMessage.data 2 (deviceFixedAttrs d) (some [part]),NlMessage.done 2 0],true) ∧
        g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d) := by
  by_cases spill : call.skb.room < nlmsgTotal 4
  · let current := paginationCompletedSocket sock call
    let doneSock : NlSock := {current with cbRunning := false, queue := [{room := NLMSG_GOODSIZE - nlmsgTotal 4,messages := [NlMessage.done 2 0]}]}
    have receiving := netlinkRecvmsg_doneOnly (some d) current call.skb
      (by simp [current,paginationCompletedSocket,spill])
      (by simp [current,paginationCompletedSocket,spill,running])
      (by simp [current,paginationCompletedSocket,spill])
      (by simp [current,paginationCompletedSocket,spill,cursor])
    have first := receiveDumpStep_data d current doneSock step messages
      2 (deviceFixedAttrs d) (some [part]) (by simpa [data,doneSock,current,paginationCompletedSocket,spill] using receiving)
    have second := netlinkRecvmsg_quiescent (some d) doneSock
      {room := NLMSG_GOODSIZE - nlmsgTotal 4,messages := [NlMessage.done 2 0]} rfl rfl
    have enoughTwo : 2 ≤ budget := by simpa only [spill,ite_true] using enough
    cases budget with
    | zero => omega
    | succ budget =>
      have tail := getterReceive_finishing d doneSock {doneSock with queue := []}
        (step+1) budget (messages.push (.data 2 (deviceFixedAttrs d) (some [part]))) none
        (by simp only [spill,ite_true] at enough; omega) (by simpa using second)
      intro g ambient pre
      obtain ⟨value,middle,midAmbient,run,valueEq,midDevice,midSocket⟩ := first g ambient pre
      subst value
      obtain ⟨result,final,after,tailRun,resultEq,finalDevice,finalSocket⟩ :=
        tail middle midAmbient ⟨midDevice,midSocket⟩
      refine ⟨result,final,after,?_,?_,finalDevice,?_⟩
      · rw [List.range'_succ,List.forIn_cons]
        change (((receiveDumpStep step (messages,false)).run g).run ambient >>= _) = _
        rw [run]
        exact tailRun
      · simp only [Option.toList_none,List.map_nil,List.nil_append] at resultEq
        change result = (messages.push (NlMessage.data 2 (deviceFixedAttrs d) (some [part])) ++
          #[NlMessage.done 2 0],true) at resultEq
        rw [Array.push_eq_append,Array.append_assoc] at resultEq
        exact resultEq
      · simpa [doneSock,current,paginationCompletedSocket,spill,cursor,sequence,
          socketReadbackFinal] using finalSocket
  · have receiving := netlinkRecvmsg_quiescent (some d) (paginationCompletedSocket sock call)
      {call.skb with room := call.skb.room - nlmsgTotal 4,messages := call.skb.messages ++ [.done 2 0]}
      (by simp [paginationCompletedSocket,spill]) (by simp [paginationCompletedSocket,spill])
    have finishing := getterReceive_finishing d (paginationCompletedSocket sock call)
      {paginationCompletedSocket sock call with queue := []} step budget messages (some part)
      (by simp only [spill,ite_false] at enough; omega) (by simpa [data] using receiving)
    intro g ambient pre
    obtain ⟨result,final,after,run,resultEq,device,socket⟩ := finishing g ambient pre
    refine ⟨result,final,after,run,?_,device,?_⟩
    · simpa only [Option.toList_some,List.map_cons,List.map_nil,List.cons_append,List.nil_append] using resultEq
    · simpa [paginationCompletedSocket,spill,cursor,sequence,socketReadbackFinal] using socket


end Leanux.Proofs.WG.Config
