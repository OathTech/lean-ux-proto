import Leanux.Proofs.WG.Config.DeviceTransitionSource
set_option autoImplicit false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- Receiving a queued page runs the next nonfinal callback before returning
the old page, retaining the exact cursor-reference Device transition. -/
theorem netlinkRecvmsg_more_device_transition (d nextDevice : Device)
    (sock : NlSock) (skb : NlSkb) (call : DumpCall)
    (queued : sock.queue = [skb]) (running : sock.cbRunning = true)
    (active : 0 < sock.dumpDoneErrno) (more : 0 < call.ret)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun g => g.dev = some d)
      (fun result g => result = call ∧ g.dev = some nextDevice)) :
    Returns (netlinkRecvmsg 7)
      (fun g => g.dev = some d ∧ g.nlSock7 = sock)
      (fun result g => result = some skb.messages ∧ g.dev = some nextDevice ∧
        g.nlSock7 = {sock with ctx := call.ctx,prevSeq := call.prevSeq, dumpDoneErrno := call.ret,queue := [call.skb]}) := by
  intro g ambient pre
  let popped : NlSock := {sock with queue := []}
  let current : WGWorld := {g with nlSock7 := popped}
  obtain ⟨value,final,after,run,device,socket⟩ :=
    netlinkDump_more_device_transition d nextDevice popped call active more callback
      current ambient ⟨pre.1,rfl⟩
  cases value
  refine ⟨some skb.messages,final,after,?_,rfl,device,?_⟩
  · simp [netlinkRecvmsg,getNlSock,pre.2,queued,setNlSock,running]
    simp only [current,popped,running] at run
    rw [run]
    rfl
  · simpa [popped] using socket

end Leanux.Proofs.WG.Config
