import Leanux.Proofs.WG.Config.DeviceDump
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
    Returns (netlinkDump 7) (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock)
      (fun _ w => w.k.wg = some d ∧ w.k.nlSock7 = completedSock sock d p) := by
  have hd := (returns_iff _ _ _).mp (wgGetDeviceDump_single pid d p peers resident empty room)
  have fit : ¬ (singlePeerDump d p).skb.room < nlmsgTotal 4 := by
    have hb := peerFixedSpace_bound p
    simp only [singlePeerDump, nlmsgTotal]
    omega
  rw [returns_iff]
  mvcgen [netlinkDump, getNlSock, getK, setNlSock, modifyK, wgGetDeviceDone,
    peerPut, branch, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [singlePeerDump, completedSock, completedChunk, nlmsgTotal]
  all_goals subst_vars
  all_goals mvcgen [hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [singlePeerDump, completedSock, completedChunk, nlmsgTotal]

  all_goals omega

theorem netlinkDumpStart_single (pid : PeerId) (d : Device) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (empty : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) :
    Returns (netlinkDumpStart 7 (byIndex d))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock ∧ selectsDevice w d)
      (fun _ w => w.k.wg = some d ∧ w.k.nlSock7 = completedSock sock d p) := by
  let started := { sock with
    cbRunning := true
    dumpDoneErrno := INT_MAX
    prevSeq := 0
    ctx := { hasWg := true } }
  have hl := lookupInterface_index d
  have hd := (returns_iff _ _ _).mp
    (netlinkDump_single pid d p started peers resident empty room rfl rfl (by change (0 : Int) < 2147483647; decide))
  rw [returns_iff]
  mvcgen [netlinkDumpStart, getNlSock, getK, setNlSock, modifyK, branch, hl, hd]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [started, completedSock]
  all_goals subst_vars
  all_goals first | exact hd _ (by simp_all [started]) | grind only

theorem netlinkRecvmsg_completed (d : Device) (p : Peer) (sock : NlSock)
    (empty : sock.queue = []) :
    Returns (netlinkRecvmsg 7)
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = completedSock sock d p)
      (fun result w => result = some (completedChunk d p).messages ∧ w.k.wg = some d ∧
        w.k.nlSock7 = { completedSock sock d p with queue := [] }) := by
  rw [returns_iff]
  mvcgen [netlinkRecvmsg, getNlSock, getK, setNlSock, modifyK]
  all_goals try dsimp +zetaDelta only at *
  all_goals repeat intro
  all_goals simp_all [completedSock]

end Leanux.Proofs.WG.Config
