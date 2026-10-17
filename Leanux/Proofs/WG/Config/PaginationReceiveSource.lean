import Leanux.Proofs.WG.Config.PaginationFinalSource
import Leanux.Proofs.WG.Config.SocketReadbackTransportSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- Receive the already queued chunk and execute the next actual nonfinal
callback before returning that old chunk. This is the repeated transport edge. -/
theorem netlinkRecvmsg_more (d : Device) (sock : NlSock) (skb : NlSkb) (call : DumpCall)
    (queued : sock.queue = [skb]) (running : sock.cbRunning = true)
    (active : 0 < sock.dumpDoneErrno) (more : 0 < call.ret)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some d)) :
    Returns (netlinkRecvmsg 7) (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some skb.messages ∧ g.dev = some d ∧
        g.nlSock7 = paginationMoreSocket sock call) := by
  intro g ambient pre
  let popped : NlSock := {sock with queue := []}
  let current : WGWorld := {g with nlSock7 := popped}
  obtain ⟨value,final,after,run,finalDevice,finalSocket⟩ :=
    netlinkDump_more d popped call active more callback current ambient ⟨pre.1,rfl⟩
  cases value
  refine ⟨some skb.messages,final,after,?_,rfl,finalDevice,?_⟩
  · simp [netlinkRecvmsg,getNlSock,pre.2,queued,setNlSock,running]
    simp only [current,popped,running] at run
    rw [run]
    rfl
  · simpa [popped,paginationMoreSocket] using finalSocket

/-- The original drain appends each ordinary DATA message to the exact
accumulator. The next socket state is the one returned by the actual receive. -/
theorem receiveDumpStep_data (d : Device) (sock nextSock : NlSock)
    (step : Nat) (messages : Array NlMessage) (flags : Nat)
    (attrs : List (String × Json)) (peers : Option (List PeerDumpAttrs))
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some [.data flags attrs peers] ∧
        g.dev = some d ∧ g.nlSock7 = nextSock)) :
    Returns (receiveDumpStep step (messages,false))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = .yield (messages.push (.data flags attrs peers),false) ∧
        g.dev = some d ∧ g.nlSock7 = nextSock) := by
  simp only [receiveDumpStep,Bool.false_eq_true,ite_false]
  apply returns_bind _ _ receive
  intro result g ambient pre
  obtain ⟨rfl,device,socket⟩ := pre
  refine ⟨_,g,ambient,?_,rfl,device,socket⟩
  simp [List.forIn_cons,List.forIn_nil]
  rfl

/-- Append a finite sequence of actual single-peer DATA receives, then its
actual finishing envelope. The bound counts that finishing receive, including
the separate-DONE case. This is source support, not a pagination headline:
the concrete callback plan must discharge every one-step receive contract. -/
theorem getterReceive_sequence (d : Device) (parts : List PeerDumpAttrs)
    (sockets : Nat → NlSock) (finalSock : NlSock) (lastMessages : List NlMessage)
    (receives : ∀ i part, parts[i]? = some part →
      Returns (netlinkRecvmsg 7)
        (fun g => g.dev = some d ∧ g.nlSock7 = sockets i)
        (fun result g => result = some [.data 2 (deviceFixedAttrs d) (some [part])] ∧
          g.dev = some d ∧ g.nlSock7 = sockets (i+1)))
    (finish : ∀ step messages, Returns (receiveDumpStep step (messages,false))
      (fun g => g.dev = some d ∧ g.nlSock7 = sockets parts.length)
      (fun result g => result = .yield (messages ++ lastMessages.toArray,true) ∧
        g.dev = some d ∧ g.nlSock7 = finalSock))
    (start budget : Nat) (messages : Array NlMessage) (within : parts.length < budget) :
    Returns (forIn (List.range' start budget) (messages,false) receiveDumpStep)
      (fun g => g.dev = some d ∧ g.nlSock7 = sockets 0)
      (fun result g => result =
        (messages ++ (parts.map (fun p => .data 2 (deviceFixedAttrs d) (some [p]))).toArray ++
          lastMessages.toArray,true) ∧ g.dev = some d ∧ g.nlSock7 = finalSock) := by
  induction parts generalizing sockets start budget messages with
  | nil =>
    cases budget with
    | zero => simp at within
    | succ budget =>
      intro g ambient pre
      obtain ⟨result,final,after,run,value,device,socket⟩ := finish start messages g ambient pre
      subst result
      refine ⟨(messages ++ lastMessages.toArray,true),final,after,?_,?_,device,socket⟩
      · rw [List.range'_succ,List.forIn_cons]
        change (((receiveDumpStep start (messages,false)).run g).run ambient >>= _) = _
        rw [run]
        change ((forIn (List.range' (start+1) budget)
          (messages ++ lastMessages.toArray,true) receiveDumpStep).run final).run after = _
        rw [receiveDump_finished]
        rfl
      · simp
  | cons part rest ih =>
    cases budget with
    | zero => simp at within
    | succ budget =>
      have first := receiveDumpStep_data d (sockets 0) (sockets 1) start messages
        2 (deviceFixedAttrs d) (some [part]) (receives 0 part (by simp))
      have nextReceives : ∀ i p, rest[i]? = some p →
          Returns (netlinkRecvmsg 7)
            (fun g => g.dev = some d ∧ g.nlSock7 = sockets (i+1))
            (fun result g => result = some [.data 2 (deviceFixedAttrs d) (some [p])] ∧
              g.dev = some d ∧ g.nlSock7 = sockets (i+1+1)) := by
        intro i p found
        exact receives (i+1) p (by simpa using found)
      have nextFinish : ∀ step acc, Returns (receiveDumpStep step (acc,false))
          (fun g => g.dev = some d ∧ g.nlSock7 = sockets (rest.length+1))
          (fun result g => result = .yield (acc ++ lastMessages.toArray,true) ∧
            g.dev = some d ∧ g.nlSock7 = finalSock) := by
        simpa only [List.length_cons] using finish
      have tailRun := ih (fun i => sockets (i+1)) nextReceives nextFinish (start+1) budget
        (messages.push (.data 2 (deviceFixedAttrs d) (some [part])))
        (by simpa using within)
      intro g ambient pre
      obtain ⟨value,current,middle,run,valueEq,device,socket⟩ := first g ambient pre
      subst value
      obtain ⟨result,final,after,restRun,resultEq,finalDevice,finalSocket⟩ :=
        tailRun current middle ⟨device,socket⟩
      refine ⟨result,final,after,?_,?_,finalDevice,finalSocket⟩
      · rw [List.range'_succ,List.forIn_cons]
        change (((receiveDumpStep start (messages,false)).run g).run ambient >>= _) = _
        rw [run]
        exact restRun
      · rw [List.map_cons, List.toArray_cons]
        rw [← Array.append_assoc]
        exact resultEq


end Leanux.Proofs.WG.Config
