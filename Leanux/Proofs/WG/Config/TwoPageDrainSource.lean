import Leanux.Proofs.WG.Config.DeviceTransitionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Append one actual complete-peer DATA and successful DONE to the drain accumulator. -/
theorem receiveDumpStep_finishing_page (d : Device) (sock nextSock : NlSock)
    (step : Nat) (messages : Array NlMessage) (attrs : List (String × Json)) (parts : Option (List PeerDumpAttrs))
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some
        ([NlMessage.data 2 attrs parts] ++ [NlMessage.done 2 0]) ∧
        g.dev = some d ∧ g.nlSock7 = nextSock)) :
    Returns (receiveDumpStep step (messages,false))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = .yield
        (messages ++ ([NlMessage.data 2 attrs parts] ++
          [NlMessage.done 2 0]).toArray,true) ∧ g.dev = some d ∧ g.nlSock7 = nextSock) := by
  simp only [receiveDumpStep,Bool.false_eq_true,ite_false]
  apply returns_bind _ _ receive
  intro result g ambient pre
  obtain ⟨rfl,device,socket⟩ := pre
  refine ⟨_,g,ambient,?_,rfl,device,socket⟩
  simp [List.forIn_cons,List.forIn_nil]
  all_goals simp only [Array.push_eq_append,Array.append_assoc]; rfl

/-- The final DATA/DONE receive finishes the original remaining loop at any positive budget. -/
theorem getterReceive_finishing_page (d : Device) (sock nextSock : NlSock)
    (step budget : Nat) (messages : Array NlMessage) (attrs : List (String × Json)) (parts : Option (List PeerDumpAttrs))
    (positive : 0 < budget)
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some
        ([NlMessage.data 2 attrs parts] ++
          [NlMessage.done 2 0]) ∧ g.dev = some d ∧ g.nlSock7 = nextSock)) :
    Returns (forIn (List.range' step budget) (messages,false) receiveDumpStep)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result =
        (messages ++ ([NlMessage.data 2 attrs parts] ++
          [NlMessage.done 2 0]).toArray,true) ∧ g.dev = some d ∧ g.nlSock7 = nextSock) := by
  cases budget with
  | zero => omega
  | succ budget =>
    intro g ambient pre
    obtain ⟨result,final,after,run,value,device,socket⟩ :=
      receiveDumpStep_finishing_page d sock nextSock step messages attrs parts receive g ambient pre
    subst result
    refine ⟨_,final,after,?_,rfl,device,socket⟩
    rw [List.range'_succ,List.forIn_cons]
    change (((receiveDumpStep step (messages,false)).run g).run ambient >>= _) = _
    rw [run]
    change ((forIn (List.range' (step+1) budget) (_,true) receiveDumpStep).run final).run after = _
    rw [receiveDump_finished]
    rfl

/-- A completed page takes one actual receive with inline DONE, or two with a separate DONE. -/
theorem getterReceive_completed_page (d : Device) (sock : NlSock) (call : DumpCall)
    (attrs : List (String × Json)) (parts : Option (List PeerDumpAttrs)) (step budget : Nat) (messages : Array NlMessage)
    (running : sock.cbRunning = true) (cursor : call.ctx = {hasWg := true})
    (sequence : call.prevSeq = d.deviceUpdateGen)
    (data : call.skb.messages = [.data 2 attrs parts])
    (enough : (if call.skb.room < nlmsgTotal 4 then 2 else 1) ≤ budget) :
    Returns (forIn (List.range' step budget) (messages,false) receiveDumpStep)
      (fun g => g.dev = some d ∧ g.nlSock7 = paginationCompletedSocket sock call)
      (fun result g => result =
        (messages ++ #[NlMessage.data 2 attrs parts,NlMessage.done 2 0],true) ∧
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
      2 attrs parts (by simpa [data,doneSock,current,paginationCompletedSocket,spill] using receiving)
    have second := netlinkRecvmsg_quiescent (some d) doneSock
      {room := NLMSG_GOODSIZE - nlmsgTotal 4,messages := [NlMessage.done 2 0]} rfl rfl
    have enoughTwo : 2 ≤ budget := by simpa only [spill,ite_true] using enough
    cases budget with
    | zero => omega
    | succ budget =>
      have tail := getterReceive_finishing d doneSock {doneSock with queue := []}
        (step+1) budget (messages.push (.data 2 attrs parts)) none
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
        change result = (messages.push (NlMessage.data 2 attrs parts) ++
          #[NlMessage.done 2 0],true) at resultEq
        rw [Array.push_eq_append,Array.append_assoc] at resultEq
        exact resultEq
      · simpa [doneSock,current,paginationCompletedSocket,spill,cursor,sequence,
          socketReadbackFinal] using finalSocket
  · have receiving := netlinkRecvmsg_quiescent (some d) (paginationCompletedSocket sock call)
      {call.skb with room := call.skb.room - nlmsgTotal 4,messages := call.skb.messages ++ [.done 2 0]}
      (by simp [paginationCompletedSocket,spill]) (by simp [paginationCompletedSocket,spill])
    have finishing := getterReceive_finishing_page d (paginationCompletedSocket sock call)
      {paginationCompletedSocket sock call with queue := []} step budget messages attrs parts
      (by simp only [spill,ite_false] at enough; omega) (by simpa [data] using receiving)
    intro g ambient pre
    obtain ⟨result,final,after,run,resultEq,device,socket⟩ := finishing g ambient pre
    refine ⟨result,final,after,run,?_,device,?_⟩
    · exact resultEq
    · simpa [paginationCompletedSocket,spill,cursor,sequence,socketReadbackFinal] using socket


/-- The unchanged first receive and its finite remaining receive budget. -/
def getterDrainAfterFirst (budget : Nat) : WG.M (Except Int Json) := do
  let first ← receiveDumpStep 0 (#[],false)
  let (messages,finished) ← match first with
    | .done acc => pure acc
    | .yield acc => forIn (List.range' 1 budget) acc receiveDumpStep
  if !finished then invariant "op 9: the dump did not finish"
  coalesce messages.toList

/-- The actual drain consumes a first DATA whose receive changes the Device,
then the completed final page with its inline or separate DONE. The two
receive/producer contracts are premises of this source composition only. -/
theorem getterDrain_two_pages_budget_source (d nextDevice : Device) (sock baseSock : NlSock)
    (call : DumpCall) (firstAttrs lastAttrs : List (String × Json))
    (firstParts lastParts : Option (List PeerDumpAttrs)) (json : Json) (budget : Nat)
    (enough : (if call.skb.room < nlmsgTotal 4 then 2 else 1) ≤ budget)
    (running : baseSock.cbRunning = true) (cursor : call.ctx = {hasWg := true})
    (sequence : call.prevSeq = nextDevice.deviceUpdateGen)
    (data : call.skb.messages = [.data 2 lastAttrs lastParts])
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some [.data 2 firstAttrs firstParts] ∧
        g.dev = some nextDevice ∧ g.nlSock7 = paginationCompletedSocket baseSock call))
    (coalesced : coalesce [.data 2 firstAttrs firstParts,.data 2 lastAttrs lastParts,.done 2 0] =
      pure (.ok json)) :
    Returns (getterDrainAfterFirst budget) (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = .ok json ∧ g.dev = some nextDevice ∧
        g.nlSock7 = socketReadbackFinal baseSock nextDevice) := by
  have first := receiveDumpStep_data_device_transition d nextDevice sock
    (paginationCompletedSocket baseSock call) 0 #[] 2 firstAttrs firstParts receive
  have last := getterReceive_completed_page nextDevice baseSock call lastAttrs lastParts
    1 budget #[NlMessage.data 2 firstAttrs firstParts] running cursor sequence data
    enough
  intro g ambient pre
  obtain ⟨value,middle,inputs,firstRun,valueEq,device,socket⟩ := first g ambient pre
  subst value
  obtain ⟨result,final,after,run,value,finalDevice,finalSocket⟩ :=
    last middle inputs ⟨device,socket⟩
  subst result
  refine ⟨.ok json,final,after,?_,rfl,finalDevice,finalSocket⟩
  unfold getterDrainAfterFirst
  change (((receiveDumpStep 0 (#[],false)).run g).run ambient >>= _) = _
  rw [firstRun]
  change (((forIn (List.range' 1 budget)
    (#[NlMessage.data 2 firstAttrs firstParts],false) receiveDumpStep).run middle).run inputs >>= _) = _
  rw [run]
  change ((coalesce [.data 2 firstAttrs firstParts,.data 2 lastAttrs lastParts,.done 2 0]).run final).run after = _
  rw [coalesced]
  rfl

/-- Specialize the symbolic composition to the original 4096-receive drain, without reducing the concrete range. -/
theorem getterDrain_two_pages_source (d nextDevice : Device) (sock baseSock : NlSock)
    (call : DumpCall) (firstAttrs lastAttrs : List (String × Json))
    (firstParts lastParts : Option (List PeerDumpAttrs)) (json : Json)
    (running : baseSock.cbRunning = true) (cursor : call.ctx = {hasWg := true})
    (sequence : call.prevSeq = nextDevice.deviceUpdateGen)
    (data : call.skb.messages = [.data 2 lastAttrs lastParts])
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some [.data 2 firstAttrs firstParts] ∧
        g.dev = some nextDevice ∧ g.nlSock7 = paginationCompletedSocket baseSock call))
    (coalesced : coalesce [.data 2 firstAttrs firstParts,.data 2 lastAttrs lastParts,.done 2 0] =
      pure (.ok json)) :
    Returns getterDrainSource (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = .ok json ∧ g.dev = some nextDevice ∧
        g.nlSock7 = socketReadbackFinal baseSock nextDevice) := by
  rw [getterDrain_first]
  exact getterDrain_two_pages_budget_source d nextDevice sock baseSock call
    firstAttrs lastAttrs firstParts lastParts json 4095 (by split <;> omega)
    running cursor sequence data receive coalesced

end Leanux.Proofs.WG.Config
