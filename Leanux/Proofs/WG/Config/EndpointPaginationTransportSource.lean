import Leanux.Proofs.WG.Config.PaginationChainSource
import Leanux.Proofs.WG.Config.PaginationStartSource

set_option autoImplicit false
set_option pp.structureInstances false
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Noise Lean Std.Do

/-- The original start performs selection and the first real callback. -/
theorem netlinkDumpStart_more_empty (d : Device) (sock : NlSock) (call : DumpCall)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) (more : 0 < call.ret)
    (callback : Returns (wgGetDeviceDump {hasWg := true} 0 {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some d)) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun _ g => g.dev = some d ∧ g.nlSock7 = paginationMoreSocket
        {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}} call) := by
  intro g ambient pre
  obtain ⟨device, socket, selected⟩ := pre
  let mark (a : Ambient) (site : Decision) (value : Bool) := {a with steps := a.steps.push {
    decision := site, outcome := value, netRx := a.netRxSection}}
  let looked := mark (mark (mark (mark (mark (mark (mark ambient
    .lookupBothOrNeither false) .lookupHasIfindex true) .lookupNoDev false)
    .lookupNoLinkOps false) .lookupNoKind false) .lookupKindMismatch false) .lookupNotWireguard false
  have lookupRun : ((lookupInterface (byIndex d)).run g).run ambient = .ok ((.ok (), g), looked) := by
    simp [selectsDevice] at selected
    simp [lookupInterface, byIndex, netDevices, device, selected, WG.orM,
      branch, AmbientM.branch, looked, mark]
    rfl
  let started := {sock with cbRunning := true, dumpDoneErrno := INT_MAX, prevSeq := 0, ctx := {hasWg := true}}
  let before := mark looked .getStartErr false
  let current := {g with nlSock7 := started}
  obtain ⟨value, final, after, run, hd, hs⟩ :=
    netlinkDump_more d started call
      (by change (0 : Int) < 2147483647; decide)
      more callback current before ⟨device, rfl⟩
  cases value
  refine ⟨(), final, after, ?_, hd, ?_⟩
  · simp [netlinkDumpStart, getNlSock, socket, idle]
    rw [lookupRun]
    change ((netlinkDump 7).run current).run before = _
    exact run
  · simpa [started,paginationMoreSocket,empty] using hs

/-- Actual start, finite drain and coalescing for a complete first callback.
The callback premise is internal source support and is discharged by callers. -/
theorem getter_completed_callback_returns (d : Device) (sock : NlSock) (call : DumpCall)
    (part : PeerDumpAttrs) (json : Json)
    (idle : sock.cbRunning = false) (empty : sock.queue = [])
    (completed : call.ret = 0) (cursor : call.ctx = {hasWg := true})
    (sequence : call.prevSeq = d.deviceUpdateGen)
    (data : call.skb.messages = [.data 2 (deviceFixedAttrs d) (some [part])])
    (callback : Returns (wgGetDeviceDump {hasWg := true} 0 {})
      (fun g => g.dev = some d) (fun result g => result = call ∧ g.dev = some d))
    (coalesced : coalesce [.data 2 (deviceFixedAttrs d) (some [part]),.done 2 0] = pure (.ok json)) :
    Returns (wgGetDevice (byIndex d))
      (fun g => g.dev = some d ∧ g.nlSock7 = sock ∧ selectsDevice g d)
      (fun result g => result = .ok json ∧ g.dev = some d ∧ g.nlSock7 = socketReadbackFinal sock d) := by
  let started : NlSock := {sock with cbRunning := true,dumpDoneErrno := INT_MAX,prevSeq := 0,ctx := {hasWg := true}}
  have drain := getterReceive_completed d started call part 0 4096 #[] rfl cursor sequence data
    (by split <;> decide)
  rw [wgGetDevice_source]
  refine returns_bind _ _ (netlinkDumpStart_completed_empty d sock call idle empty completed
    (by rw [cursor]) callback) ?_
  intro _ g ambient pre
  obtain ⟨value,final,after,run,valueEq,device,socket⟩ := drain g ambient pre
  simp only [Array.empty_append] at valueEq
  subst value
  refine ⟨.ok json,final,after,?_,rfl,device,?_⟩
  · rw [getterDrain_range_source]
    change (((forIn (List.range' 0 4096) (#[],false) receiveDumpStep).run g).run ambient >>= _) = _
    rw [run]
    change ((coalesce [.data 2 (deviceFixedAttrs d) (some [part]),.done 2 0]).run final).run after = _
    rw [coalesced]
    rfl
  · simpa [started,socketReadbackFinal] using socket
end Leanux.Proofs.WG.Config
