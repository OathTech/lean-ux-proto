import Leanux.Proofs.WG.Config.PaginationCompletionSource

set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- A positive original callback queues its DATA and transports its exact final Device. -/
theorem netlinkDump_more_device_transition (d nextDevice : Device) (sock : NlSock) (call : DumpCall)
    (active : 0 < sock.dumpDoneErrno) (more : 0 < call.ret)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun w => w.dev = some d) (fun q w => q = call ∧ w.dev = some nextDevice)) :
    Returns (netlinkDump 7) (fun w => w.dev = some d ∧ w.nlSock7 = sock)
      (fun _ w => w.dev = some nextDevice ∧ w.nlSock7 =
        { sock with ctx := call.ctx, prevSeq := call.prevSeq, dumpDoneErrno := call.ret, queue := sock.queue ++ [call.skb] }) := by
  intro g ambient pre
  obtain ⟨device, socket⟩ := pre
  obtain ⟨result, current, after, run, value, hd⟩ := callback g ambient device
  subst result
  let final := {current with nlSock7 :=
    {sock with ctx := call.ctx, prevSeq := call.prevSeq, dumpDoneErrno := call.ret, queue := sock.queue ++ [call.skb]}}
  refine ⟨(), final, after, ?_, hd, rfl⟩
  simp [netlinkDump, getNlSock, socket, active]
  rw [run]
  dsimp only [bind, Except.bind]
  simp [more, setNlSock, final]
  rfl

/-- The completed callback may change the Device; insufficient DONE room queues DATA without running the finalizer. -/
theorem netlinkDump_completed_spill_device_transition (d nextDevice : Device) (sock : NlSock) (call : DumpCall)
    (active : 0 < sock.dumpDoneErrno) (completed : call.ret = 0)
    (short : call.skb.room < nlmsgTotal 4)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some nextDevice)) :
    Returns (netlinkDump 7) (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun _ g => g.dev = some nextDevice ∧ g.nlSock7 =
        {sock with ctx := call.ctx, prevSeq := call.prevSeq, dumpDoneErrno := 0, queue := sock.queue ++ [call.skb]}) := by
  intro g ambient pre
  obtain ⟨device,socket⟩ := pre
  obtain ⟨result,current,after,run,value,finalDevice⟩ := callback g ambient device
  subst result
  let final : WGWorld := {current with nlSock7 := {sock with ctx := call.ctx, prevSeq := call.prevSeq, dumpDoneErrno := 0, queue := sock.queue ++ [call.skb]}}
  refine ⟨(),final,after,?_,finalDevice,rfl⟩
  simp [netlinkDump,getNlSock,socket,active]
  rw [run]
  dsimp only [bind,Except.bind]
  simp [completed,short,setNlSock,final]
  rfl

/-- The fitting completed path transports the callback Device through actual DONE and the null-cursor finalizer. -/
theorem netlinkDump_completed_fits_device_transition (d nextDevice : Device) (sock : NlSock) (call : DumpCall)
    (active : 0 < sock.dumpDoneErrno) (completed : call.ret = 0)
    (fits : nlmsgTotal 4 ≤ call.skb.room) (cursor : call.ctx.nextPeer = none)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some nextDevice)) :
    Returns (netlinkDump 7) (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun _ g => g.dev = some nextDevice ∧ g.nlSock7 =
        {sock with ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := 0,cbRunning := false, queue := sock.queue ++ [{call.skb with room := call.skb.room - nlmsgTotal 4, messages := call.skb.messages ++ [.done 2 0]}]}) := by
  intro g ambient pre
  obtain ⟨device,socket⟩ := pre
  obtain ⟨result,current,after,run,value,finalDevice⟩ := callback g ambient device
  subst result
  let final : WGWorld := {current with nlSock7 :=
    {sock with ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := 0,cbRunning := false, queue := sock.queue ++ [{call.skb with room := call.skb.room - nlmsgTotal 4, messages := call.skb.messages ++ [.done 2 0]}]}}
  let marked := {after with steps := after.steps.push {
    decision := .getDoneHasWg,outcome := call.ctx.hasWg,netRx := after.netRxSection}}
  let inputs := {marked with steps := marked.steps.push {
    decision := .peerPutNull,outcome := true,netRx := marked.netRxSection}}
  have enough : ¬ call.skb.room < nlmsgTotal 4 := by omega
  refine ⟨(),final,inputs,?_,finalDevice,rfl⟩
  simp [netlinkDump,getNlSock,socket,active]
  rw [run]
  dsimp only [bind,Except.bind]
  simp [completed,enough,setNlSock,wgGetDeviceDone,cursor,
    peerPut,branch,AmbientM.branch,final,marked,inputs]
  rfl

/-- Receiving the old page executes the actual completing callback, including either DONE-room branch, before returning that page. -/
theorem netlinkRecvmsg_completing_device_transition (d nextDevice : Device) (sock : NlSock) (skb : NlSkb) (call : DumpCall)
    (queued : sock.queue = [skb]) (running : sock.cbRunning = true)
    (active : 0 < sock.dumpDoneErrno) (completed : call.ret = 0)
    (cursor : call.ctx.nextPeer = none)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some nextDevice)) :
    Returns (netlinkRecvmsg 7) (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some skb.messages ∧ g.dev = some nextDevice ∧
        g.nlSock7 = paginationCompletedSocket sock call) := by
  intro g ambient pre
  let popped : NlSock := {sock with queue := []}
  let current : WGWorld := {g with nlSock7 := popped}
  by_cases spill : call.skb.room < nlmsgTotal 4
  · obtain ⟨value,final,after,run,finalDevice,finalSocket⟩ :=
      netlinkDump_completed_spill_device_transition d nextDevice popped call active completed spill callback
        current ambient ⟨pre.1,rfl⟩
    cases value
    refine ⟨some skb.messages,final,after,?_,rfl,finalDevice,?_⟩
    · simp [netlinkRecvmsg,getNlSock,pre.2,queued,setNlSock,running]
      simp only [current,popped,running] at run
      rw [run]
      rfl
    · simpa [popped,paginationCompletedSocket,spill] using finalSocket
  · obtain ⟨value,final,after,run,finalDevice,finalSocket⟩ :=
      netlinkDump_completed_fits_device_transition d nextDevice popped call active completed (by omega) cursor callback
        current ambient ⟨pre.1,rfl⟩
    cases value
    refine ⟨some skb.messages,final,after,?_,rfl,finalDevice,?_⟩
    · simp [netlinkRecvmsg,getNlSock,pre.2,queued,setNlSock,running]
      simp only [current,popped,running] at run
      rw [run]
      rfl
    · simpa [popped,paginationCompletedSocket,spill] using finalSocket

/-- The drain appends its actual received DATA and retains the Device returned by that receive. -/
theorem receiveDumpStep_data_device_transition (d nextDevice : Device) (sock nextSock : NlSock)
    (step : Nat) (messages : Array NlMessage) (flags : Nat)
    (attrs : List (String × Json)) (peers : Option (List PeerDumpAttrs))
    (receive : Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some [.data flags attrs peers] ∧
        g.dev = some nextDevice ∧ g.nlSock7 = nextSock)) :
    Returns (receiveDumpStep step (messages,false))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = .yield (messages.push (.data flags attrs peers),false) ∧
        g.dev = some nextDevice ∧ g.nlSock7 = nextSock) := by
  simp only [receiveDumpStep,Bool.false_eq_true,ite_false]
  apply returns_bind _ _ receive
  intro result g ambient pre
  obtain ⟨rfl,device,socket⟩ := pre
  refine ⟨_,g,ambient,?_,rfl,device,socket⟩
  simp [List.forIn_cons,List.forIn_nil]
  rfl


/-- The actual idle start selects the original Device and transports a
nonfinal callback's possibly changed Device and exact queued chunk. -/
theorem netlinkDumpStart_more_device_transition (d nextDevice : Device)
    (sock : NlSock) (call : DumpCall) (idle : sock.cbRunning = false)
    (more : 0 < call.ret)
    (callback : Returns (wgGetDeviceDump {hasWg := true} 0 {})
      (fun g => g.dev = some d)
      (fun result g => result = call ∧ g.dev = some nextDevice)) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun _ g => g.dev = some nextDevice ∧ g.nlSock7 =
        {sock with cbRunning := true,ctx := call.ctx,prevSeq := call.prevSeq,dumpDoneErrno := call.ret,queue := sock.queue ++ [call.skb]}) := by
  intro g ambient pre
  obtain ⟨device,socket,selected⟩ := pre
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site,outcome := value,netRx := a.netRxSection}}
  let looked := mark (mark (mark (mark (mark (mark (mark ambient
    .lookupBothOrNeither false) .lookupHasIfindex true) .lookupNoDev false)
    .lookupNoLinkOps false) .lookupNoKind false) .lookupKindMismatch false) .lookupNotWireguard false
  have lookupRun : ((lookupInterface (byIndex d)).run g).run ambient = .ok ((.ok (),g),looked) := by
    simp [selectsDevice] at selected
    simp [lookupInterface,byIndex,netDevices,device,selected,WG.orM,
      branch,AmbientM.branch,looked,mark]
    rfl
  let started := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
  let before := mark looked .getStartErr false
  let current := {g with nlSock7 := started}
  obtain ⟨value,final,after,run,deviceAfter,socketAfter⟩ :=
    netlinkDump_more_device_transition d nextDevice started call
      (by change (0 : Int) < 2147483647; decide) more callback current before ⟨device,rfl⟩
  cases value
  refine ⟨(),final,after,?_,deviceAfter,?_⟩
  · simp [netlinkDumpStart,getNlSock,socket,idle]
    rw [lookupRun]
    change ((netlinkDump 7).run current).run before = _
    exact run
  · exact socketAfter

end Leanux.Proofs.WG.Config
