import Leanux.Proofs.WG.Config.GetterSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- A completing callback whose DATA leaves less than the real DONE size
queues that DATA unchanged and preserves the callback-running flag. It does not
run done. -/
theorem netlinkDump_completed_spill (d : Device) (sock : NlSock) (call : DumpCall)
    (active : 0 < sock.dumpDoneErrno) (completed : call.ret = 0)
    (short : call.skb.room < nlmsgTotal 4)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some d)) :
    Returns (netlinkDump 7) (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun _ g => g.dev = some d ∧ g.nlSock7 =
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

/-- Once the callback has finished, the next socket dump emits only DONE.
The original nonpositive errno is retained; no callback is run on this path. -/
theorem netlinkDump_doneOnly (device : Option Device) (sock : NlSock)
    (completed : sock.dumpDoneErrno ≤ 0) (cursor : sock.ctx.nextPeer = none) :
    Returns (netlinkDump 7) (fun g => g.dev = device ∧ g.nlSock7 = sock)
      (fun _ g => g.dev = device ∧ g.nlSock7 =
        {sock with cbRunning := false,queue := sock.queue ++
          [{room := NLMSG_GOODSIZE - nlmsgTotal 4,messages := [.done 2 sock.dumpDoneErrno]}]}) := by
  intro g ambient pre
  let final : WGWorld := {g with nlSock7 :=
    {sock with cbRunning := false,queue := sock.queue ++
      [{room := NLMSG_GOODSIZE - nlmsgTotal 4,messages := [.done 2 sock.dumpDoneErrno]}]}}
  let marked := {ambient with steps := ambient.steps.push {
    decision := .getDoneHasWg,outcome := sock.ctx.hasWg,netRx := ambient.netRxSection}}
  let after := {marked with steps := marked.steps.push {
    decision := .peerPutNull,outcome := true,netRx := marked.netRxSection}}
  have notActive : ¬ 0 < sock.dumpDoneErrno := by omega
  refine ⟨(),final,after,?_,pre.1,rfl⟩
  simp [netlinkDump,getNlSock,pre.2,notActive,NLMSG_GOODSIZE,nlmsgTotal,
    setNlSock,wgGetDeviceDone,cursor,peerPut,branch,AmbientM.branch,marked,after,final]
  rfl

/-- Receiving an already queued chunk after callback completion invokes the
DONE-only path before returning that chunk. The exact nonpositive completion
errno is not erased. -/
theorem netlinkRecvmsg_doneOnly (device : Option Device) (sock : NlSock) (skb : NlSkb)
    (queued : sock.queue = [skb]) (running : sock.cbRunning = true)
    (completed : sock.dumpDoneErrno ≤ 0) (cursor : sock.ctx.nextPeer = none) :
    Returns (netlinkRecvmsg 7) (fun g => g.dev = device ∧ g.nlSock7 = sock)
      (fun result g => result = some skb.messages ∧ g.dev = device ∧ g.nlSock7 =
        {sock with cbRunning := false,queue :=
          [{room := NLMSG_GOODSIZE - nlmsgTotal 4,messages := [.done 2 sock.dumpDoneErrno]}]}) := by
  intro g ambient pre
  let popped : NlSock := {sock with queue := []}
  let current : WGWorld := {g with nlSock7 := popped}
  obtain ⟨value,final,after,run,finalDevice,finalSocket⟩ :=
    netlinkDump_doneOnly device popped completed cursor current ambient ⟨pre.1,rfl⟩
  cases value
  refine ⟨some skb.messages,final,after,?_,rfl,finalDevice,?_⟩
  · simp [netlinkRecvmsg,getNlSock,pre.2,queued,setNlSock,running]
    simp only [current,popped,running] at run
    rw [run]
    rfl
  · simpa [popped] using finalSocket

end Leanux.Proofs.WG.Config
