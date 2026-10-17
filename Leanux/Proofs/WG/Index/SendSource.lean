import Leanux.Proofs.WG.Index.TablePreservationSource
import Leanux.Proofs.WG.Index.SendFrames
import Leanux.Proofs.WG.Index.OwnerCreation
import Leanux.Proofs.WG.Index.PeerReleaseTableFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem sendHandshakeInitiation_tables (pid : PeerId) : Ensures (sendHandshakeInitiation pid)
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hc := createInitiation_tables pid
  have hm := addMacToPacket_tables pid
  have ht := traversal_tables pid
  have hd := delKeepalive_tables pid
  have hs := sendBufferToPeer_tables pid
  have hf := timersHandshakeInitiated_tables pid
  have hh := hiddenClock64_kernel_spec TablesSafeKernel
  have hp := setPeer_tables
  rw [ensures_iff]
  mvcgen [sendHandshakeInitiation, branchExpired, birthdateTest, getPeer, getDev, getK,
    branch, branchCmp, invariant, hc, hm, ht, hd, hs, hf, hh, hp]

theorem handshakeSendWorker_tables (pid : PeerId) : Ensures (handshakeSendWorker pid)
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hs := (ensures_iff _ _ _).mp (sendHandshakeInitiation_tables pid)
  have hp := peerPut_tables
  rw [ensures_iff]
  mvcgen [handshakeSendWorker, hs, hp]

end Leanux.Proofs.WG.Index
