import Leanux.Proofs.WG.Config.DeviceDumpFrames
import Leanux.Proofs.WG.Config.DeviceScalars

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

def completedChunk (d : Device) (p : Peer) : NlSkb :=
  let skb := (singlePeerDump d p).skb
  { skb with room := skb.room - 20, messages := skb.messages ++ [.done 2 0] }

def completedSock (old : NlSock) (d : Device) (p : Peer) : NlSock :=
  { old with queue := old.queue ++ [completedChunk d p]
             ctx := { hasWg := true }, prevSeq := d.deviceUpdateGen
             dumpDoneErrno := 0, cbRunning := false }

theorem peerFixedSpace_bound (p : Peer) : peerFixedSpace p ≤ 168 := by
  unfold peerFixedSpace
  split <;> (try split) <;> omega

theorem netlinkDump_single (pid : PeerId) (d : Device) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (ctx : sock.ctx = { hasWg := true }) (seq : sock.prevSeq = 0)
    (active : 0 < sock.dumpDoneErrno) :
    Returns (netlinkDump 7) (fun w => w.dev = some d ∧ w.nlSock7 = sock)
      (fun _ w => w.dev = some d ∧ w.nlSock7 = completedSock sock d p) := by
  intro g ambient pre
  obtain ⟨device, socket⟩ := pre
  obtain ⟨result, current, after, run, value, hd, hs⟩ :=
    wgGetDeviceDump_single_framed pid d p peers resident empty room
      (fun g => g.nlSock7 = sock) g ambient ⟨device, socket⟩
  subst result
  have fit : ¬ (singlePeerDump d p).skb.room < nlmsgTotal 4 := by
    have hb := peerFixedSpace_bound p
    simp only [singlePeerDump, nlmsgTotal]
    omega
  let final := {current with nlSock7 := completedSock sock d p}
  let marked := {after with steps := after.steps.push {
    decision := .getDoneHasWg, outcome := true, netRx := after.netRxSection}}
  let finish := {marked with steps := marked.steps.push {
    decision := .peerPutNull, outcome := true, netRx := marked.netRxSection}}
  refine ⟨(), final, finish, ?_, hd, rfl⟩
  simp [netlinkDump, getNlSock, socket, active, ctx, seq]
  rw [run]
  dsimp only [bind, Except.bind]
  have fits : ¬ NLMSG_GOODSIZE - devicePrefixSpace d - peerFixedSpace p < 20 := fit
  simp [singlePeerDump, completedChunk, completedSock, fits, nlmsgTotal,
    wgGetDeviceDone, peerPut, branch, AmbientM.branch, setNlSock,
    final, finish, marked]
  rfl


theorem netlinkDumpStart_single (pid : PeerId) (d : Device) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun w => w.dev = some d ∧ w.nlSock7 = sock ∧ selectsDevice w d)
      (fun _ w => w.dev = some d ∧ w.nlSock7 = completedSock sock d p) := by
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
  let started := {sock with
    cbRunning := true
    dumpDoneErrno := INT_MAX
    prevSeq := 0
    ctx := {hasWg := true}}
  let before := mark looked .getStartErr false
  let current := {g with nlSock7 := started}
  obtain ⟨value, final, after, run, hd, hs⟩ :=
    netlinkDump_single pid d p started peers resident empty room rfl rfl
      (by change (0 : Int) < 2147483647; decide)
      current before ⟨device, rfl⟩
  cases value
  refine ⟨(), final, after, ?_, hd, ?_⟩
  · simp [netlinkDumpStart, getNlSock, socket, idle]
    rw [lookupRun]
    change ((netlinkDump 7).run current).run before = _
    exact run
  · simpa [started, completedSock] using hs

theorem netlinkRecvmsg_completed (d : Device) (p : Peer) (sock : NlSock)
    (empty : sock.queue = []) :
    Returns (netlinkRecvmsg 7)
      (fun w => w.dev = some d ∧ w.nlSock7 = completedSock sock d p)
      (fun result w => result = some (completedChunk d p).messages ∧ w.dev = some d ∧
        w.nlSock7 = {completedSock sock d p with queue := []}) := by
  intro g ambient pre
  refine ⟨some (completedChunk d p).messages,
    {g with nlSock7 := {completedSock sock d p with queue := []}}, ambient,
    ?_, rfl, pre.1, rfl⟩
  simp [netlinkRecvmsg, getNlSock, setNlSock, pre.2, completedSock, empty]
  rfl

end Leanux.Proofs.WG.Config
