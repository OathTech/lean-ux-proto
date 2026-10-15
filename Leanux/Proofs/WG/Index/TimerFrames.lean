import Leanux.Proofs.WG.Index.ClearFrames
import Leanux.Proofs.WG.Index.ReceiveFrames

set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Index
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem delTimer_tables (pid : PeerId) (timer : PeerTimer) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ delTimer pid timer
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  mvcgen [delTimer, getPeer, getDev, getK, invariant, hp]

theorem clearPeerEndpointSrc_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ clearPeerEndpointSrc pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  have hd := dstCacheReset_tables
  mvcgen [clearPeerEndpointSrc, dstCacheResetNow, getPeer, getDev, getK, invariant, hp, hd]

theorem purgeStagedPackets_tables (pid : PeerId) :
    ⦃fun w => ⌜TablesSafeKernel w.k⌝⦄ purgeStagedPackets pid
      ⦃⇓? _ w => ⌜TablesSafeKernel w.k⌝⦄ := by
  have hp := setPeer_tables
  mvcgen [purgeStagedPackets, getPeer, getDev, getK, invariant, modifyDev, modifyK, hp]
  all_goals try dsimp +zetaDelta only at *
  all_goals simp_all [TablesSafeKernel, DeviceTablesSafe, KeypairOwnersBounded]
  all_goals grind

end Leanux.Proofs.WG.Index
