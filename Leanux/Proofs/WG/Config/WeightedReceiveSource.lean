import Leanux.Proofs.WG.Config.WeightedStartSource
import Leanux.Proofs.WG.Config.WeightedPaginationSource
import Leanux.Proofs.WG.Config.GenericPaginationClaims

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- A derived finite family of original receive contracts. Its length counts
the finishing envelope, including a separate DONE envelope when required.
It is constructed from callbacks below, never supplied to a public getter. -/
def WeightedReceiveReceipt (d : Device) (initial final : NlSock)
    (messages : List NlMessage) (count : Nat) : Prop :=
  ∃ (parts : List PeerDumpAttrs) (sockets : Nat → NlSock) (last : Option PeerDumpAttrs),
    sockets 0 = initial ∧ parts.length + 1 = count ∧
    parts.map (fun p => NlMessage.data 2 (deviceFixedAttrs d) (some [p])) ++
      last.toList.map (fun p => NlMessage.data 2 (deviceFixedAttrs d) (some [p])) ++
      [NlMessage.done 2 0] = messages ∧
    (∀ i part, parts[i]? = some part → Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sockets i)
      (fun result g => result = some [.data 2 (deviceFixedAttrs d) (some [part])] ∧
        g.dev = some d ∧ g.nlSock7 = sockets (i+1))) ∧
    (∀ step acc, Returns (receiveDumpStep step (acc,false))
      (fun g => g.dev = some d ∧ g.nlSock7 = sockets parts.length)
      (fun result g => result = .yield
        (acc ++ (last.toList.map (fun p => NlMessage.data 2 (deviceFixedAttrs d) (some [p])) ++
          [NlMessage.done 2 0]).toArray,true) ∧ g.dev = some d ∧ g.nlSock7 = final))

/-- Prefix one already-derived original receive; this does not induct over
the getter loop. -/
theorem weightedReceiveReceipt_prepend (d : Device) (initial middle final : NlSock)
    (part : PeerDumpAttrs) (messages : List NlMessage) (count : Nat)
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = initial)
      (fun result g => result = some [.data 2 (deviceFixedAttrs d) (some [part])] ∧
        g.dev = some d ∧ g.nlSock7 = middle))
    (tail : WeightedReceiveReceipt d middle final messages count) :
    WeightedReceiveReceipt d initial final
      (.data 2 (deviceFixedAttrs d) (some [part]) :: messages) (count+1) := by
  obtain ⟨parts,sockets,last,start,length,output,receives,finish⟩ := tail
  let next : Nat → NlSock := fun i => match i with | 0 => initial | j+1 => sockets j
  refine ⟨part::parts,next,last,rfl,by simp [length],?_,?_,?_⟩
  · simpa only [List.map_cons,List.cons_append] using congrArg
      (List.cons (.data 2 (deviceFixedAttrs d) (some [part]))) output
  · intro i found equal
    cases i with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at equal; subst found
              simpa [next,start] using receive
    | succ i => exact receives i found (by simpa using equal)
  · simpa only [List.length_cons,next] using finish

/-- Exact completed DATA reception: one receive for inline DONE, two for a
spill. Both contracts come from the original socket operations. -/
theorem weightedReceiveReceipt_completed (d : Device) (sock : NlSock)
    (call : DumpCall) (part : PeerDumpAttrs)
    (running : sock.cbRunning = true) (cursor : call.ctx = {hasWg := true})
    (sequence : call.prevSeq = d.deviceUpdateGen)
    (data : call.skb.messages = [.data 2 (deviceFixedAttrs d) (some [part])]) :
    WeightedReceiveReceipt d (paginationCompletedSocket sock call) (socketReadbackFinal sock d)
      [.data 2 (deviceFixedAttrs d) (some [part]),.done 2 0]
      (if call.skb.room < nlmsgTotal 4 then 2 else 1) := by
  by_cases spill : call.skb.room < nlmsgTotal 4
  · let current := paginationCompletedSocket sock call
    let doneSock : NlSock := {current with cbRunning := false, queue := [{room := NLMSG_GOODSIZE - nlmsgTotal 4,messages := [NlMessage.done 2 0]}]}
    have receive := netlinkRecvmsg_doneOnly (some d) current call.skb
      (by simp [current,paginationCompletedSocket,spill])
      (by simp [current,paginationCompletedSocket,spill,running])
      (by simp [current,paginationCompletedSocket,spill])
      (by simp [current,paginationCompletedSocket,spill,cursor])
    have quiet := netlinkRecvmsg_quiescent (some d) doneSock
      {room := NLMSG_GOODSIZE - nlmsgTotal 4,messages := [NlMessage.done 2 0]} rfl rfl
    have tail : WeightedReceiveReceipt d doneSock (socketReadbackFinal sock d) [NlMessage.done 2 0] 1 := by
      refine ⟨[],fun _ => doneSock,none,rfl,rfl,rfl,?_,?_⟩
      · intro i p h; simp at h
      · intro step acc
        simpa [doneSock,current,paginationCompletedSocket,spill,cursor,sequence,socketReadbackFinal]
          using receiveDumpStep_finishing d doneSock {doneSock with queue := []} step acc none quiet
    simpa only [spill,ite_true] using weightedReceiveReceipt_prepend d current doneSock
      (socketReadbackFinal sock d) part [NlMessage.done 2 0] 1
      (by simpa [doneSock,current,paginationCompletedSocket,spill,data] using receive) tail
  · let current := paginationCompletedSocket sock call
    have quiet := netlinkRecvmsg_quiescent (some d) current
      {call.skb with room := call.skb.room - nlmsgTotal 4,messages := call.skb.messages ++ [NlMessage.done 2 0]}
      (by simp [current,paginationCompletedSocket,spill])
      (by simp [current,paginationCompletedSocket,spill])
    refine ⟨[],fun _ => current,some part,rfl,by simp [spill],rfl,?_,?_⟩
    · intro i p h; simp at h
    · intro step acc
      simpa [current,paginationCompletedSocket,spill,cursor,sequence,socketReadbackFinal,data]
        using receiveDumpStep_finishing d current {current with queue := []} step acc (some part)
          (by simpa [data] using quiet)

/-- Instantiate the existing generic receive-loop proof, preserving the
receipt's exact envelope count and messages. -/
theorem weightedReceiveReceipt_run (d : Device) (initial final : NlSock)
    (messages : List NlMessage) (count budget : Nat)
    (receipt : WeightedReceiveReceipt d initial final messages count) (enough : count ≤ budget) :
    Returns (forIn (List.range' 0 budget) (#[],false) receiveDumpStep)
      (fun g => g.dev = some d ∧ g.nlSock7 = initial)
      (fun result g => result = (messages.toArray,true) ∧ g.dev = some d ∧ g.nlSock7 = final) := by
  obtain ⟨parts,sockets,last,start,length,output,receives,finish⟩ := receipt
  have run := getterReceive_sequence d parts sockets final
    (last.toList.map (fun p => .data 2 (deviceFixedAttrs d) (some [p])) ++ [NlMessage.done 2 0])
    receives finish 0 budget #[] (by omega)
  simpa only [Array.empty_append,List.append_toArray,List.nil_append,← List.append_assoc,output,start] using run

end Leanux.Proofs.WG.Config
