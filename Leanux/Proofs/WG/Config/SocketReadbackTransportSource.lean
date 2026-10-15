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
      (fun w => w.k.wg = some d) (fun q w => q = call ∧ w.k.wg = some d)) :
    Returns (netlinkDump 7) (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock)
      (fun _ w => w.k.wg = some d ∧ w.k.nlSock7 =
        { sock with ctx := call.ctx, prevSeq := call.prevSeq, dumpDoneErrno := call.ret, queue := sock.queue ++ [call.skb] }) := by
  have hd := (returns_iff _ _ _).mp callback
  rw [returns_iff]
  mvcgen [netlinkDump, getNlSock, getK, setNlSock, modifyK, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all
  all_goals subst_vars
  all_goals mvcgen [hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all

/-- A completing callback supplies its own DATA; the original socket code
appends DONE, runs the null-cursor finalizer and clears cbRunning. -/
theorem netlinkDump_last (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) (sock : NlSock) (active : 0 < sock.dumpDoneErrno)
    (room : devicePrefixSpace d + 44 + 28 * ids.length + 20 ≤ NLMSG_GOODSIZE)
    (callback : Returns (wgGetDeviceDump sock.ctx sock.prevSeq {})
      (fun w => w.k.wg = some d)
      (fun q w => q = socketLastCall d p nodes ids ∧ w.k.wg = some d)) :
    Returns (netlinkDump 7) (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock)
      (fun _ w => w.k.wg = some d ∧ w.k.nlSock7 = socketLastState sock d p nodes ids) := by
  have hd := (returns_iff _ _ _).mp callback
  have fit : ¬ (socketLastCall d p nodes ids).skb.room < nlmsgTotal 4 := by
    simp only [socketLastCall, nlmsgTotal]
    omega
  rw [returns_iff]
  mvcgen [netlinkDump, getNlSock, getK, setNlSock, modifyK, wgGetDeviceDone,
    peerPut, branch, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [socketLastCall, socketLastState, socketLastChunk, nlmsgTotal]
  all_goals subst_vars
  all_goals mvcgen [hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [socketLastCall, socketLastState, socketLastChunk, nlmsgTotal]
  all_goals omega

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
      (fun w => w.k.wg = some d)
      (fun q w => q = socketFirstCall d p nodes front b ∧ w.k.wg = some d)) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock ∧ selectsDevice w d)
      (fun _ w => w.k.wg = some d ∧ w.k.nlSock7 = socketFirstState sock d p nodes front b) := by
  let started := { sock with cbRunning := true, dumpDoneErrno := INT_MAX, prevSeq := 0, ctx := { hasWg := true } }
  have hl := lookupInterface_index d
  have hd := (returns_iff _ _ _).mp (netlinkDump_more d started
    (socketFirstCall d p nodes front b) (by change (0 : Int) < 2147483647; decide)
    (socketFirstCall_positive d p nodes front b) callback)
  rw [returns_iff]
  mvcgen [netlinkDumpStart, getNlSock, getK, setNlSock, modifyK, branch, hl, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [started, socketFirstState]
  all_goals subst_vars
  all_goals first | exact hd _ (by simp_all [started]) | grind only

/-- Pop the first DATA chunk and execute the next callback before returning
that chunk. This is the original receive path, not a supplied second envelope. -/
theorem netlinkRecvmsg_front (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (front : List NodeId) (b : NodeId) (tail : List NodeId) (sock : NlSock)
    (empty : sock.queue = [])
    (room : devicePrefixSpace d + 44 + 28 * (b :: tail).length + 20 ≤ NLMSG_GOODSIZE)
    (callback : Returns (wgGetDeviceDump
        { hasWg := true, nextAllowedip := some b, allowedipsSeq := d.peerAllowedips.seq }
        d.deviceUpdateGen {}) (fun w => w.k.wg = some d)
      (fun q w => q = socketLastCall d p nodes (b :: tail) ∧ w.k.wg = some d)) :
    Returns (netlinkRecvmsg 7)
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = socketFirstState sock d p nodes front b)
      (fun q w => q = some (socketFirstCall d p nodes front b).skb.messages ∧
        w.k.wg = some d ∧ w.k.nlSock7 = socketLastState sock d p nodes (b :: tail)) := by
  have hd := (returns_iff _ _ _).mp (netlinkDump_last d p nodes (b :: tail)
    { socketFirstState sock d p nodes front b with queue := [] }
    (socketFirstCall_positive d p nodes front b) room callback)
  rw [returns_iff]
  mvcgen [netlinkRecvmsg, getNlSock, getK, setNlSock, modifyK, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [socketFirstState, socketLastState, socketFirstCall]
  all_goals subst_vars
  all_goals mvcgen [hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [socketFirstState, socketLastState, socketFirstCall]

theorem netlinkRecvmsg_last (d : Device) (p : Peer) (nodes : NodeId → AipNode)
    (ids : List NodeId) (sock : NlSock) (empty : sock.queue = []) :
    Returns (netlinkRecvmsg 7)
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = socketLastState sock d p nodes ids)
      (fun q w => q = some (socketLastChunk d p nodes ids).messages ∧
        w.k.wg = some d ∧ w.k.nlSock7 = socketReadbackFinal sock d) := by
  rw [returns_iff]
  mvcgen [netlinkRecvmsg, getNlSock, getK, setNlSock, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [socketLastState, socketReadbackFinal]

end Leanux.Proofs.WG.Config
