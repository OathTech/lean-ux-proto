import Leanux.Proofs.WG.Config.PaginationCompletionSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- The actual idle-socket start selects the device, initializes its callback,
and transports a completing first callback through the real DONE room test.
Preexisting queued envelopes are retained before the new DATA/DONE envelope.
The callback is the original operation; no socket or Ambient frame is assumed. -/
theorem netlinkDumpStart_completed (d : Device) (sock : NlSock) (call : DumpCall)
    (idle : sock.cbRunning = false) (completed : call.ret = 0)
    (cursor : call.ctx.nextPeer = none)
    (callback : Returns (wgGetDeviceDump {hasWg := true} 0 {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some d)) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun _ g => g.dev = some d ∧
        let started := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
        let completedSock := paginationCompletedSocket started call
        g.nlSock7 = {completedSock with queue := sock.queue ++ completedSock.queue}) := by
  intro g ambient pre
  obtain ⟨device,socket,selected⟩ := pre
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site,outcome := value,netRx := a.netRxSection}}
  let looked := mark (mark (mark (mark (mark (mark (mark ambient
    .lookupBothOrNeither false) .lookupHasIfindex true) .lookupNoDev false)
    .lookupNoLinkOps false) .lookupNoKind false) .lookupKindMismatch false) .lookupNotWireguard false
  have lookupRun : ((lookupInterface (byIndex d)).run g).run ambient = .ok ((.ok (),g),looked) := by
    simp [selectsDevice] at selected
    simp [lookupInterface,byIndex,netDevices,device,selected,WG.orM,branch,AmbientM.branch,looked,mark]
    rfl
  let started := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
  let before := mark looked .getStartErr false
  let current := {g with nlSock7 := started}
  have dump : Returns (netlinkDump 7)
      (fun state => state.dev = some d ∧ state.nlSock7 = started)
      (fun _ state => state.dev = some d ∧
        state.nlSock7 = {paginationCompletedSocket started call with
          queue := sock.queue ++ (paginationCompletedSocket started call).queue}) := by
    by_cases spill : call.skb.room < nlmsgTotal 4
    · intro state inputs pre
      obtain ⟨value,final,after,run,finalDevice,finalSocket⟩ :=
        netlinkDump_completed_spill d started call (by change (0 : Int) < 2147483647; decide)
          completed spill callback state inputs pre
      refine ⟨value,final,after,run,finalDevice,?_⟩
      simpa [started,paginationCompletedSocket,spill] using finalSocket
    · intro state inputs pre
      obtain ⟨value,final,after,run,finalDevice,finalSocket⟩ :=
        netlinkDump_completed_fits d started call (by change (0 : Int) < 2147483647; decide)
          completed (by omega) cursor callback state inputs pre
      refine ⟨value,final,after,run,finalDevice,?_⟩
      simpa [started,paginationCompletedSocket,spill] using finalSocket
  obtain ⟨value,final,after,run,finalDevice,finalSocket⟩ := dump current before ⟨device,rfl⟩
  cases value
  refine ⟨(),final,after,?_,finalDevice,finalSocket⟩
  simp [netlinkDumpStart,getNlSock,socket,idle]
  rw [lookupRun]
  change ((netlinkDump 7).run current).run before = _
  exact run

/-- With an initially empty receive queue, completion is exactly the existing
pagination socket state, including its inline-DONE versus later-DONE branch. -/
theorem netlinkDumpStart_completed_empty (d : Device) (sock : NlSock) (call : DumpCall)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (completed : call.ret = 0) (cursor : call.ctx.nextPeer = none)
    (callback : Returns (wgGetDeviceDump {hasWg := true} 0 {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some d)) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun _ g => g.dev = some d ∧ g.nlSock7 = paginationCompletedSocket
        {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}} call) := by
  simpa only [empty,List.nil_append] using
    netlinkDumpStart_completed d sock call idle completed cursor callback

end Leanux.Proofs.WG.Config
