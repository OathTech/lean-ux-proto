import Leanux.Proofs.WG.Config.AllowedRootRemoval

/-! Existing preservation support, separated from state-changing effects. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem rootLeafRemoved_table (v4 : Bool) (d : Device) (id : NodeId) (n : AipNode) :
    (rootLeafRemoved v4 d id n).peerAllowedips =
      if v4 then { d.peerAllowedips with root4 := none, seq := d.peerAllowedips.seq + 1 }
      else { d.peerAllowedips with root6 := none, seq := d.peerAllowedips.seq + 1 } := by
  cases v4 <;> simp [rootLeafRemoved, rootNodeRemoved, deleteListedNodes_allowedips, bumpAllowedips]

theorem rootLeafRemoved_running (v4 : Bool) (d : Device) (id : NodeId) (n : AipNode) :
    (rootLeafRemoved v4 d id n).running = d.running := by
  simpa [rootLeafRemoved, rootNodeRemoved, withoutPeers, bumpAllowedips] using
    congrArg Device.running (deleteListedNodes_withoutPeers id (bumpAllowedips d) (bumpAllowedips d).peers.toList)

end Leanux.Proofs.WG.Config
