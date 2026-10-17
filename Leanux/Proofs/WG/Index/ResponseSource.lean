import Leanux.Proofs.WG.Index.TablePreservationSource
import Leanux.Proofs.WG.Index.ResponseFrames
import Leanux.Proofs.WG.Index.SendSource

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

/-- Compose response creation, session installation and the original send/timer suffix. -/
theorem sendHandshakeResponse_tables (pid : PeerId) : Ensures (sendHandshakeResponse pid)
    (fun w => TablesSafeKernel w.k) (fun _ w => TablesSafeKernel w.k) := by
  have hc := createResponse_tables pid
  have hb := beginSession_tables pid
  have hm := addMacToPacket_tables pid
  have hsession := timersSessionDerived_tables pid
  have ht := traversal_tables pid
  have hd := delKeepalive_tables pid
  have hs := sendBufferToPeer_tables pid
  have hh := hiddenClock64_kernel_spec TablesSafeKernel
  have hp := setPeer_tables
  rw [ensures_iff]
  mvcgen [sendHandshakeResponse, getPeer, getDev, getK, branch, invariant,
    hc, hb, hm, hsession, ht, hd, hs, hh, hp]

end Leanux.Proofs.WG.Index
