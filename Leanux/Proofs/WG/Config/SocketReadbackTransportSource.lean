import Leanux.Proofs.WG.Config.SocketReadbackCallsSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048
namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

/-- A positive original callback queues DATA and leaves this socket running. -/
theorem netlinkDump_more (d : Device) (sock : NlSock) (call : DumpCall)
    (active : 0 < sock.dumpDoneErrno) (more : 0 < call.ret)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun w => w.dev = some d) (fun q w => q = call ∧ w.dev = some d)) :
    Returns (netlinkDump 7) (fun w => w.dev = some d ∧ w.nlSock7 = sock)
      (fun _ w => w.dev = some d ∧ w.nlSock7 =
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


/-- A completing callback supplies its own DATA; the original socket code
appends DONE, runs the null-cursor finalizer and clears cbRunning. -/
theorem netlinkDump_last (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) (sock : NlSock) (active : 0 < sock.dumpDoneErrno)
    (room : devicePrefixSpace d + 44 + 28 * ids.length + 20 ≤ NLMSG_GOODSIZE)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun w => w.dev = some d)
      (fun q w => q = socketLastCall d p nodes ids ∧ w.dev = some d)) :
    Returns (netlinkDump 7) (fun w => w.dev = some d ∧ w.nlSock7 = sock)
      (fun _ w => w.dev = some d ∧ w.nlSock7 = socketLastState sock d p nodes ids) := by
  intro g ambient pre
  obtain ⟨device, socket⟩ := pre
  obtain ⟨result, current, after, run, value, hd⟩ := callback g ambient device
  subst result
  have fit : ¬ (socketLastCall d p nodes ids).skb.room < nlmsgTotal 4 := by
    simp only [socketLastCall, nlmsgTotal]
    omega
  let final := {current with nlSock7 := socketLastState sock d p nodes ids}
  let marked := {after with steps := after.steps.push {
    decision := .getDoneHasWg, outcome := true, netRx := after.netRxSection}}
  let finish := {marked with steps := marked.steps.push {
    decision := .peerPutNull, outcome := true, netRx := marked.netRxSection}}
  refine ⟨(), final, finish, ?_, hd, rfl⟩
  simp [netlinkDump, getNlSock, socket, active]
  rw [run]
  dsimp only [bind, Except.bind]
  have fits : ¬ NLMSG_GOODSIZE - (devicePrefixSpace d + 44 + 28 * ids.length) < 20 := fit
  simp [socketLastCall, socketLastChunk, socketLastState, fits, nlmsgTotal,
    wgGetDeviceDone, peerPut, branch, AmbientM.branch, setNlSock, final, finish, marked]
  rfl


theorem socketFirstCall_positive (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) : 0 < (socketFirstCall d p nodes front b).ret := by
  simp only [socketFirstCall]
  apply Int.natCast_pos.mpr
  unfold NLMSG_GOODSIZE
  omega

/-- The original start performs selection and the first real callback. -/
theorem netlinkDumpStart_front (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (sock : NlSock) (idle : sock.cbRunning = false)
    (callback : Returns (wgGetDeviceDump { hasWg := true } 0 {})
      (fun w => w.dev = some d)
      (fun q w => q = socketFirstCall d p nodes front b ∧ w.dev = some d)) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun w => w.dev = some d ∧ w.nlSock7 = sock ∧ selectsDevice w d)
      (fun _ w => w.dev = some d ∧ w.nlSock7 = socketFirstState sock d p nodes front b) := by
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
    netlinkDump_more d started (socketFirstCall d p nodes front b)
      (by change (0 : Int) < 2147483647; decide)
      (socketFirstCall_positive d p nodes front b) callback current before ⟨device, rfl⟩
  cases value
  refine ⟨(), final, after, ?_, hd, ?_⟩
  · simp [netlinkDumpStart, getNlSock, socket, idle]
    rw [lookupRun]
    change ((netlinkDump 7).run current).run before = _
    exact run
  · simpa [started, socketFirstState] using hs


/-- Pop the first DATA chunk and execute the next callback before returning
that chunk. This is the original receive path, not a supplied second envelope. -/
theorem netlinkRecvmsg_front (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId) (sock : NlSock)
    (empty : sock.queue = [])
    (room : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (callback : Returns (wgGetDeviceDump
        { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
        d.deviceUpdateGen {}) (fun w => w.dev = some d)
      (fun q w => q = socketLastCall d p nodes (b :: tail) ∧ w.dev = some d)) :
    Returns (netlinkRecvmsg 7)
      (fun w => w.dev = some d ∧ w.nlSock7 = socketFirstState sock d p nodes front b)
      (fun q w => q = some (socketFirstCall d p nodes front b).skb.messages ∧
        w.dev = some d ∧ w.nlSock7 = socketLastState sock d p nodes (b :: tail)) := by
  intro g ambient pre
  obtain ⟨device, socket⟩ := pre
  let popped := {socketFirstState sock d p nodes front b with queue := []}
  let current := {g with nlSock7 := popped}
  obtain ⟨value, final, after, run, hd, hs⟩ :=
    netlinkDump_last d p nodes (b :: tail) popped
      (socketFirstCall_positive d p nodes front b) room callback current ambient ⟨device, rfl⟩
  cases value
  refine ⟨some (socketFirstCall d p nodes front b).skb.messages, final, after, ?_, rfl, hd, ?_⟩
  · simp [netlinkRecvmsg, getNlSock, setNlSock, socket, socketFirstState, empty]
    change (((netlinkDump 7).run current).run ambient >>= _) = _
    rw [run]
    rfl
  · simpa [socketLastState, popped, socketFirstState, empty] using hs


theorem netlinkRecvmsg_last (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) (sock : NlSock) (empty : sock.queue = []) :
    Returns (netlinkRecvmsg 7)
      (fun w => w.dev = some d ∧ w.nlSock7 = socketLastState sock d p nodes ids)
      (fun q w => q = some (socketLastChunk d p nodes ids).messages ∧
        w.dev = some d ∧ w.nlSock7 = socketReadbackFinal sock d) := by
  intro g ambient pre
  refine ⟨some (socketLastChunk d p nodes ids).messages,
    {g with nlSock7 := socketReadbackFinal sock d}, ambient, ?_, rfl, pre.1, rfl⟩
  simp [netlinkRecvmsg, getNlSock, setNlSock, pre.2, socketLastState, socketReadbackFinal, empty]
  rfl


end Leanux.Proofs.WG.Config
