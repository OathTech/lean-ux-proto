import Leanux.Proofs.WG.Config.DumpTransport
import Leanux.Proofs.WG.Config.GetterSource

set_option pp.structureInstances false
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Lean Std.Do

theorem receiveDumpStep_single (d : Device) (p : Peer) (sock : NlSock)
    (empty : sock.queue = []) :
    Returns (receiveDumpStep 0 (#[], false))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = completedSock sock d p)
      (fun result w => result = .yield ((completedChunk d p).messages.toArray, true) ∧
        w.k.wg = some d ∧ w.k.nlSock7 = { completedSock sock d p with queue := [] }) := by
  simp only [receiveDumpStep, Bool.false_eq_true, if_false]
  apply returns_bind _ _ (netlinkRecvmsg_completed d p sock empty)
  intro result
  rw [returns_iff]
  intro w h
  obtain ⟨heq, hd, hs⟩ := h
  subst result
  simp [completedChunk, singlePeerDump, List.forIn_cons, List.forIn_nil]
  exact ⟨hd, hs⟩

theorem getterDrain_single (d : Device) (p : Peer) (sock : NlSock)
    (empty : sock.queue = []) :
    Returns getterDrainSource
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = completedSock sock d p)
      (fun result w => result = .ok (singlePeerJson d p) ∧
        w.k.wg = some d ∧ w.k.nlSock7 = { completedSock sock d p with queue := [] }) := by
  have hc : coalesce [.data 2 (deviceFixedAttrs d)
      (some [{ publicKey := hexKey p.remoteStatic, attrs := peerFixedAttrs p }]), .done 2 0] =
      pure (.ok (singlePeerJson d p)) := coalesce_single d p
  rw [getterDrain_first]
  apply returns_bind _ _ (receiveDumpStep_single d p sock empty)
  intro result
  rw [returns_iff]
  intro w h
  obtain ⟨heq, hd, hs⟩ := h
  subst result
  simp [receiveDump_finished, completedChunk, singlePeerDump, hc]
  exact ⟨hd, hs⟩

theorem wgGetDevice_single (pid : PeerId) (d : Device) (p : Peer) (sock : NlSock)
    (peers : d.peerList = [pid]) (resident : d.peers[pid]? = some p)
    (noIps : p.allowedipsList = []) (room : devicePrefixSpace d + 168 + 20 ≤ NLMSG_GOODSIZE)
    (idle : sock.cbRunning = false) (empty : sock.queue = []) :
    Returns (wgGetDevice (byIndex d))
      (fun w => w.k.wg = some d ∧ w.k.nlSock7 = sock ∧ selectsDevice w d)
      (fun result w => result = .ok (singlePeerJson d p) ∧ w.k.wg = some d ∧
        w.k.nlSock7 = { completedSock sock d p with queue := [] }) := by
  rw [wgGetDevice_source]
  exact returns_bind _ _ (netlinkDumpStart_single pid d p sock peers resident noIps room idle)
    (fun _ => getterDrain_single d p sock empty)

end Leanux.Proofs.WG.Config
