import Leanux.Proofs.WG.Config.AllowedLists
import Leanux.Proofs.WG.Config.Model

/-! Existing preservation support, separated from state-changing effects. -/
set_option autoImplicit false
set_option pp.structureInstances false
set_option maxHeartbeats 800000

namespace Leanux.Proofs.WG.Config
open Leanux Leanux.WG Leanux.Proofs.WG.Noise Std.Do

theorem deleteListedNodes_withoutPeers (id : NodeId) (d : Device) (entries : List (PeerId × Peer)) :
    withoutPeers (deleteListedNodes id d entries) = withoutPeers d := by
  induction entries generalizing d with
  | nil => rfl
  | cons entry rest ih =>
      simp only [deleteListedNodes, List.foldl_cons]
      change withoutPeers (deleteListedNodes id (deleteListedNode id d entry) rest) = _
      rw [ih]
      unfold deleteListedNode
      split <;> rfl

theorem deleteListedNodes_nodes (id : NodeId) (d : Device) (entries : List (PeerId × Peer)) :
    (deleteListedNodes id d entries).nodes = d.nodes := by
  simpa only [withoutPeers] using congrArg Device.nodes (deleteListedNodes_withoutPeers id d entries)

theorem deleteListedNodes_allowedips (id : NodeId) (d : Device) (entries : List (PeerId × Peer)) :
    (deleteListedNodes id d entries).peerAllowedips = d.peerAllowedips := by
  simpa only [withoutPeers] using congrArg Device.peerAllowedips (deleteListedNodes_withoutPeers id d entries)

end Leanux.Proofs.WG.Config
